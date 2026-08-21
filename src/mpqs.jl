# Multiple Polynomial Quadratic Sieve (MPQS) for integer factorization
# Ref: Silverman (1987) "The Multiple Polynomial Quadratic Sieve"
# Ref: Pomerance (1982) "Analysis and Comparison of Some Integer Factoring Algorithms"
# Ref: Knuth & Trabb Pardo (1976) "Analysis of a Simple Factorization Algorithm"
# Ref: Crandall & Pomerance (2005) "Prime Numbers: A Computational Perspective", Ch.6

"""
Context for MPQS factorization.
"""
mutable struct MPQSContext
    n::BigInt           # kn (multiplied)
    n_orig::BigInt      # original n
    k::Int              # Knuth multiplier
    factor_base::Vector{Int}
    fb_size::Int
    sqrt_kn_mod::Vector{Int}
    log_primes::Vector{UInt8}
    sieve_interval::Int
end

"""
A smooth or partially-smooth relation found during sieving.
large_prime == 0: fully smooth relation
large_prime > 0, large_prime2 == 0: single large prime partial
large_prime > 0, large_prime2 > 0: double large prime partial (large_prime < large_prime2)
"""
struct SmoothRelation
    # ax + b, reduced mod n once the relation is kept. Always a BigInt: combining two
    # partials multiplies these mod n, which needs the full width of n even when the
    # polynomial arithmetic itself runs in a fixed-width type.
    ax_plus_b::BigInt
    exponents::BitVector # parity of exponents over factor base
    full_exp::Vector{Int32} # actual exponent counts of g(x) over factor base
    a_indices::Vector{Int}  # FB indices of primes composing polynomial `a`
    large_prime::Int     # first unfactored prime (0 if fully smooth)
    large_prime2::Int    # second unfactored prime (0 if single LP or smooth)
end

"""
Represents an MPQS polynomial Q(x) = (ax + b)² - kn, in the working type `T`.
`c = (b² - kn) / a`, so g(x) = Q(x)/a = a·x² + 2b·x + c is evaluated without
ever forming Q(x) itself.
"""
struct MPQSPolynomial{T<:Integer}
    a::T
    b::T
    c::T
    a_factors::Vector{Int}  # indices into factor base for primes composing a
end

# c = (b² - kn) / a. |c| ≈ M·√(kn/2) so the result fits T, but b² alone is ~2kn/M²
# and would overflow it — so the intermediate is formed in BigInt and narrowed after.
# Once per polynomial, against a full sieve pass, so the promotion is free.
function _poly_c(::Type{T}, b::Integer, kn::BigInt, a_big::BigInt) where {T<:Integer}
    bb = BigInt(b)
    return T(div(bb * bb - kn, a_big))
end

# Precomputed table: digit count → (fb_size, sieve_interval)
# Ref: Silverman (1987), Crandall & Pomerance (2005) Ch.6
# Standard MPQS parameters: factor base sizes from L-smoothness formula.
# Large prime variation significantly amplifies effective relation yield.
# Ref: L-smoothness formula calibrated against reference implementations
const _MPQS_PARAMS = [
    (digits=30, fb_size=200,   sieve_interval=55000),
    (digits=35, fb_size=400,   sieve_interval=55000),
    (digits=40, fb_size=700,   sieve_interval=55000),
    (digits=45, fb_size=1200,  sieve_interval=55000),
    (digits=50, fb_size=1900,  sieve_interval=66000),
    (digits=55, fb_size=2900,  sieve_interval=66000),
    (digits=58, fb_size=3700,  sieve_interval=95000),
    (digits=60, fb_size=5500,  sieve_interval=250000),
    (digits=62, fb_size=6200,  sieve_interval=250000),
    (digits=65, fb_size=7500,  sieve_interval=250000),
    (digits=68, fb_size=9000,  sieve_interval=250000),
    (digits=70, fb_size=10000, sieve_interval=250000),
    (digits=73, fb_size=13000, sieve_interval=250000),
    (digits=76, fb_size=16000, sieve_interval=250000),
]

"""
Select MPQS parameters (factor base size, sieve interval) based on digit count.
"""
function _mpqs_select_params(n::BigInt)
    d = ndigits(n)
    # Find bracketing entries and interpolate
    if d <= _MPQS_PARAMS[1].digits
        return _MPQS_PARAMS[1].fb_size, _MPQS_PARAMS[1].sieve_interval
    end
    if d >= _MPQS_PARAMS[end].digits
        return _MPQS_PARAMS[end].fb_size, _MPQS_PARAMS[end].sieve_interval
    end
    for i in 1:(length(_MPQS_PARAMS) - 1)
        lo, hi = _MPQS_PARAMS[i], _MPQS_PARAMS[i + 1]
        if lo.digits <= d <= hi.digits
            t = (d - lo.digits) / (hi.digits - lo.digits)
            fb = round(Int, lo.fb_size + t * (hi.fb_size - lo.fb_size))
            si = round(Int, lo.sieve_interval + t * (hi.sieve_interval - lo.sieve_interval))
            return fb, si
        end
    end
    return _MPQS_PARAMS[end].fb_size, _MPQS_PARAMS[end].sieve_interval
end

"""
Select optimal Knuth multiplier for MPQS.
Scores k ∈ {1,3,5,...,47} using Silverman's formula.
Ref: Silverman (1987) §4
"""
function _select_knuth_multiplier(n::BigInt)::Int
    best_k = 1
    best_score = -Inf
    small_primes = primes(200)

    for k in 1:2:47
        kn = BigInt(k) * n
        score = 0.0

        # Special handling for p=2
        kn_mod8 = Int(mod(kn, 8))
        if kn_mod8 == 1
            score += 2 * log(2.0)
        elseif kn_mod8 == 5
            score += log(2.0)
        end

        # Score odd primes
        for p in small_primes
            p == 2 && continue
            if mod(k, p) == 0
                score += log(Float64(p)) / p
            elseif powermod(kn, div(p - 1, 2), p) == 1  # Legendre(kn, p) == 1
                score += 2 * log(Float64(p)) / p
            end
        end

        # Penalize large k slightly
        score -= 0.5 * log(Float64(k))

        if score > best_score
            best_score = score
            best_k = k
        end
    end
    return best_k
end

"""
Build factor base: primes p where Legendre(kn, p) == 1, plus p=2.
Also computes sqrt(kn) mod p and log₂(p) for each prime.
"""
function _build_factor_base(kn::Integer, fb_size_target::Int)
    factor_base = Int[2]
    sqrt_kn_mod = Int[mod(kn, 2) == 0 ? 0 : 1]

    p = 3
    while length(factor_base) < fb_size_target
        if isprime(p) && powermod(kn, div(p - 1, 2), p) == 1
            push!(factor_base, p)
            # kn mod p fits in an Int, so the root is found in machine arithmetic
            push!(sqrt_kn_mod, _tonelli_shanks(Int(mod(kn, p)), p))
        end
        p += 2
    end

    log_primes = UInt8[floor(UInt8, log2(p)) for p in factor_base]

    return factor_base, sqrt_kn_mod, log_primes
end

"""
Tonelli-Shanks algorithm for computing square root mod p.
Returns r such that r² ≡ n (mod p).
"""
function _tonelli_shanks(n::Int, p::Int)::Int
    n = mod(n, p)
    n == 0 && return 0
    p == 2 && return n

    # Factor out powers of 2 from p-1
    q = p - 1
    s = 0
    while iseven(q)
        q >>= 1
        s += 1
    end

    if s == 1
        # p ≡ 3 (mod 4)
        return powermod(n, div(p + 1, 4), p)
    end

    # Find a non-residue z
    z = 2
    while powermod(z, div(p - 1, 2), p) != p - 1
        z += 1
    end

    M = s
    c = powermod(z, q, p)
    t = powermod(n, q, p)
    R = powermod(n, div(q + 1, 2), p)

    while true
        t == 1 && return R
        # Find least i such that t^(2^i) ≡ 1 (mod p)
        i = 0
        temp = t
        while temp != 1
            temp = Int(mod(widemul(temp, temp), p))
            i += 1
        end
        b = powermod(c, 1 << (M - i - 1), p)
        M = i
        c = Int(mod(widemul(b, b), p))
        t = Int(mod(widemul(t, c), p))
        R = Int(mod(widemul(R, b), p))
    end
end

"""
Root-guided trial factoring of g(x), which is held in the working type `T`.
`exponents` and `full_exp` are zeroed and filled in-place to avoid allocation.
Returns a SmoothRelation or nothing.
"""
@inline function _trial_factor_guided(ax_b::T, gx::T, n_orig::BigInt, ctx::MPQSContext,
                               large_prime_bound::Int, dlp_bound::Int, dlp_bound_sq::Int,
                               sieve_pos::Int,
                               starts1::Vector{Int}, starts2::Vector{Int},
                               a_indices::Vector{Int},
                               exponents::BitVector, full_exp::Vector{Int32}
                               )::Union{SmoothRelation, Nothing} where {T<:Integer}
    fb = ctx.factor_base
    fb_size = ctx.fb_size

    # Reset buffers
    fill!(exponents, false)
    fill!(full_exp, Int32(0))
    remainder = abs(gx)

    if gx < 0
        exponents[1] = true
        full_exp[1] = Int32(1)
    end

    early_exit_j = fb_size + 1  # sentinel: no early exit
    @inbounds for j in 1:fb_size
        p = fb[j]
        pT = T(p)
        s1 = starts1[j]
        if s1 == 0
            # Prime with no stored sieve position — brute force check
            q, r = divrem(remainder, pT)
            if iszero(r)
                cnt = Int32(1)
                remainder = q
                while true
                    q, r = divrem(remainder, pT)
                    iszero(r) || break
                    cnt += Int32(1)
                    remainder = q
                end
                full_exp[j + 1] = cnt
                exponents[j + 1] = isodd(cnt)
                if isone(remainder)
                    break
                elseif remainder < pT * pT
                    early_exit_j = j
                    break
                end
            end
            continue
        end
        hit = (rem(sieve_pos - s1, p) == 0)
        if !hit
            s2 = starts2[j]
            hit = (s2 != s1) && (rem(sieve_pos - s2, p) == 0)
        end
        hit || continue

        # p divides g(x) — extract all powers
        cnt = Int32(0)
        while true
            q, r = divrem(remainder, pT)
            iszero(r) || break
            cnt += Int32(1)
            remainder = q
        end
        full_exp[j + 1] = cnt
        exponents[j + 1] = isodd(cnt)
        if isone(remainder)
            break
        elseif remainder < pT * pT
            early_exit_j = j
            break
        end
    end

    # Handle early exit: remainder has at most one prime factor
    if early_exit_j <= fb_size && !isone(remainder)
        rem_int = Int(remainder)
        idx = searchsortedfirst(fb, rem_int)
        if idx <= fb_size && fb[idx] == rem_int
            full_exp[idx + 1] += Int32(1)
            exponents[idx + 1] ⊻= true
            remainder = one(T)
        end
    end

    for ai in a_indices
        exponents[ai + 1] ⊻= true
    end

    # A relation is kept rarely enough that promoting ax+b to a BigInt here costs nothing.
    if isone(remainder)
        return SmoothRelation(mod(BigInt(ax_b), n_orig), copy(exponents), copy(full_exp), a_indices, 0, 0)
    elseif remainder <= large_prime_bound && remainder > 1
        lp = Int(remainder)
        if isprime(lp)
            return SmoothRelation(mod(BigInt(ax_b), n_orig), copy(exponents), copy(full_exp), a_indices, lp, 0)
        end
    elseif remainder <= dlp_bound_sq && remainder > 1 && !isprime(Int(remainder))
        # Double large prime: try to split composite remainder into two primes.
        # remainder ≤ dlp_bound_sq < typemax(Int), so this stays in machine arithmetic.
        # `eachfactor` rather than `lenstrafactor` directly: the remainder can be a prime
        # power or have a small factor, cases where ECM alone spins and eventually throws.
        r = Int(remainder)
        f = first(first(eachfactor(r)))
        p1 = Int(min(f, div(r, f)))
        p2 = Int(max(f, div(r, f)))
        if p1 > 1 && p2 > 1 && p1 <= dlp_bound && p2 <= dlp_bound && isprime(p1) && isprime(p2)
            return SmoothRelation(mod(BigInt(ax_b), n_orig), copy(exponents), copy(full_exp), a_indices, p1, p2)
        end
    end

    return nothing
end

"""
Combine two partial relations sharing a large prime `shared_lp`.
The shared LP cancels (appears with even exponent in the product).
Returns a relation with remaining LPs (0, 1, or 2).
"""
function _combine_partials(r1::SmoothRelation, r2::SmoothRelation,
                           shared_lp::Int, ctx::MPQSContext)::Union{SmoothRelation, Nothing}
    combined_exp = r1.exponents .⊻ r2.exponents
    combined_full = r1.full_exp .+ r2.full_exp
    combined_a_indices = vcat(r1.a_indices, r2.a_indices)
    combined_axb = mod(r1.ax_plus_b * r2.ax_plus_b, ctx.n_orig)

    # Collect remaining LPs (those that aren't the shared one)
    remaining = Int[]
    for lp in (r1.large_prime, r1.large_prime2, r2.large_prime, r2.large_prime2)
        lp == 0 && continue
        lp == shared_lp && continue
        push!(remaining, lp)
    end

    # The shared LP appears in both relations, so its product is lp^2 (even exponent).
    # We track it for square root computation.
    if isempty(remaining)
        return SmoothRelation(combined_axb, combined_exp, combined_full,
                              combined_a_indices, shared_lp, 0)
    elseif length(remaining) == 1
        return SmoothRelation(combined_axb, combined_exp, combined_full,
                              combined_a_indices, shared_lp, remaining[1])
    end
    # Two or more remaining LPs — can't use directly as a full relation
    return nothing
end

"""
GF(2) Gaussian elimination on parity vectors (fallback for small matrices).
Returns dependency sets (indices that XOR to zero).
"""
function _gf2_eliminate_gaussian(relations::Vector{BitVector}, fb_size::Int)::Vector{Vector{Int}}
    nrels = length(relations)
    nrels == 0 && return Vector{Int}[]

    matrix = [copy(r) for r in relations]
    history = [falses(nrels) for _ in 1:nrels]
    for i in 1:nrels
        history[i][i] = true
    end
    ncols = length(relations[1])
    pivot_col = zeros(Int, ncols)

    for i in 1:nrels
        pivot = findfirst(matrix[i])
        while pivot !== nothing
            if pivot_col[pivot] == 0
                pivot_col[pivot] = i
                break
            else
                pr = pivot_col[pivot]
                matrix[i] .⊻= matrix[pr]
                history[i] .⊻= history[pr]
                pivot = findfirst(matrix[i])
            end
        end
    end

    dependencies = Vector{Int}[]
    for i in 1:nrels
        if !any(matrix[i])
            push!(dependencies, findall(history[i]))
        end
    end
    return dependencies
end

"""
    _gf2_eliminate(relations, fb_size) -> Vector{Vector{Int}}

Find GF(2) dependencies using Gaussian elimination.
For the matrix sizes encountered in MPQS (up to ~10K), Gaussian elimination
is faster than Block Lanczos due to lower overhead.
"""
function _gf2_eliminate(relations::Vector{BitVector}, fb_size::Int)::Vector{Vector{Int}}
    return _gf2_eliminate_gaussian(relations, fb_size)
end

"""
Extract a factor from a dependency set using stored exponent vectors.
full_exp stores exponents of g(x) over the factor base (sign in index 1).
a_indices stores which FB primes compose the polynomial's `a` value.
Q(x) = a · g(x), so exp_Q(p) = exp_g(p) + exp_a(p).
"""
function _extract_factor(n_orig::BigInt, kn::BigInt, k::Int,
                         dependency::Vector{Int},
                         relations::Vector{SmoothRelation},
                         factor_base::Vector{Int})::Union{BigInt, Nothing}
    x = BigInt(1)
    fb_size = length(factor_base)
    total_exp = zeros(Int, fb_size)

    for idx in dependency
        r = relations[idx]
        x = mod(x * r.ax_plus_b, n_orig)

        # Add g(x) exponents (indices 2:end of full_exp, index 1 is sign)
        for j in 1:fb_size
            total_exp[j] += Int(r.full_exp[j + 1])
        end
        # Add a exponents: each prime in a_indices contributes exponent 1
        for ai in r.a_indices
            total_exp[ai] += 1
        end
    end

    # Compute y = ∏ p^(e/2) mod n (all exponents should be even by GF(2) dependency)
    y = BigInt(1)
    for j in 1:fb_size
        e = total_exp[j]
        if e > 0
            y = mod(y * powermod(BigInt(factor_base[j]), e ÷ 2, n_orig), n_orig)
        end
    end

    # Include large prime contributions from combined partial relations.
    # Each shared LP appears with even exponent (lp^2), contributing one lp to y.
    for idx in dependency
        r = relations[idx]
        if r.large_prime > 0
            y = mod(y * BigInt(r.large_prime), n_orig)
        end
        if r.large_prime2 > 0
            y = mod(y * BigInt(r.large_prime2), n_orig)
        end
    end

    g = gcd(abs(x - y), n_orig)
    if g > 1 && g < n_orig
        g2 = gcd(g, BigInt(k))
        if g2 > 1 && g2 < g
            g = div(g, g2)
        end
        if g > 1 && g < n_orig && mod(n_orig, g) == 0
            return g
        end
    end

    g = gcd(abs(x + y), n_orig)
    if g > 1 && g < n_orig
        g2 = gcd(g, BigInt(k))
        if g2 > 1 && g2 < g
            g = div(g, g2)
        end
        if g > 1 && g < n_orig && mod(n_orig, g) == 0
            return g
        end
    end

    return nothing
end

"""
Generate SIQS `a` value and CRT components for multiple b-values.
Returns (a, a_indices, B_components) where B_components[j] is the CRT contribution
from the j-th prime factor of a. This allows generating 2^(s-1) b-values.
"""
function _generate_siqs_a(::Type{T}, ctx::MPQSContext, used_a_sets::Set{Vector{Int}}) where {T<:Integer}
    fb = ctx.factor_base
    fb_size = ctx.fb_size
    kn = ctx.n
    target_a = isqrt(2 * kn) ÷ ctx.sieve_interval

    lo = max(5, fb_size ÷ 3)
    hi = fb_size
    typical_log_p = log(Float64(fb[div(lo + hi, 2)]))
    num_facs = max(2, round(Int, log(Float64(target_a)) / typical_log_p))
    num_facs_range = max(2, num_facs - 1):min(fb_size ÷ 2, num_facs + 1)

    best_a = BigInt(0)
    best_indices = Int[]
    best_diff = BigInt(10)^200

    for _ in 1:100
        nf = rand(num_facs_range)
        indices = sort(rand(lo:hi, nf))
        length(unique(indices)) == nf || continue
        indices = unique(indices)
        sort!(indices)
        length(indices) == nf || continue
        indices in used_a_sets && continue

        a = prod(BigInt(fb[i]) for i in indices)
        diff = abs(a - target_a)
        if diff < best_diff
            best_diff = diff
            best_a = a
            best_indices = indices
        end
    end

    isempty(best_indices) && return nothing
    push!(used_a_sets, best_indices)

    a = best_a
    s = length(best_indices)

    # Compute CRT components B_j via Hensel lifting:
    # For each prime q_j | a, B_j = sqrt(kn) mod q_j * (a/q_j) * inv(a/q_j, q_j) mod a
    # Selection runs in BigInt (once per a-value); the results drop into T for the sieve.
    B_components = Vector{T}(undef, s)
    for (j, idx) in enumerate(best_indices)
        q = BigInt(fb[idx])
        r = ctx.sqrt_kn_mod[idx]
        a_div_q = a ÷ q
        inv_a_q = invmod(mod(a_div_q, q), q)
        B_components[j] = T(mod(r * a_div_q * inv_a_q, a))
    end

    return (T(a), best_indices, B_components)
end

"""
Compute initial sieve root offsets from b, once per a-value.
offset1[j], offset2[j] ∈ [0, p-1]: sieve positions are offset+1, offset+1+p, ...
Use -1 as sentinel for "no root" (p | a and 2b ≡ 0 mod p).
"""
function _compute_siqs_roots!(offset1::Vector{Int}, offset2::Vector{Int},
                               b::T, c::T,
                               inv_a::Vector{Int},
                               sqrt_kn_mod::Vector{Int},
                               factor_base::Vector{Int},
                               fb_size::Int, M::Int, a_indices::Vector{Int}) where {T<:Integer}
    @inbounds for j in 1:fb_size
        p = factor_base[j]
        if inv_a[j] == 0
            b2_mod_p = mod(2 * Int(mod(b, p)), p)
            c_mod_p = Int(mod(c, p))
            if b2_mod_p == 0
                offset1[j] = -1; offset2[j] = -1
            else
                b_inv = invmod(b2_mod_p, p)
                r = mod(-c_mod_p * b_inv, p)
                o = mod(r + M, p)
                offset1[j] = o; offset2[j] = o
            end
        else
            sqr = sqrt_kn_mod[j]
            b_mod_p = Int(mod(b, p))
            ai = inv_a[j]
            r1 = mod((sqr - b_mod_p) * ai, p)
            r2 = mod((-sqr - b_mod_p) * ai, p)
            offset1[j] = mod(r1 + M, p)
            offset2[j] = mod(r2 + M, p)
        end
    end
end

"""
Fast SIQS sieve: constant initialization (fill!) + unclamped subtraction + small prime skipping.
"""
function _siqs_sieve!(sieve::Vector{UInt8}, sieve_len::Int,
                      offset1::Vector{Int}, offset2::Vector{Int},
                      starts1::Vector{Int}, starts2::Vector{Int},
                      factor_base::Vector{Int}, log_primes::Vector{UInt8},
                      fb_size::Int, sieve_start_idx::Int, log_init::UInt8)
    fill!(sieve, log_init)

    @inbounds for j in 1:fb_size
        if offset1[j] < 0
            starts1[j] = 0; starts2[j] = 0
        else
            starts1[j] = offset1[j] + 1
            starts2[j] = offset2[j] + 1
        end
    end

    @inbounds for j in sieve_start_idx:fb_size
        p = factor_base[j]
        logp = log_primes[j]
        s1 = starts1[j]
        s1 <= 0 && continue

        s2 = starts2[j]
        if s2 != s1 && s2 > 0
            # Two distinct roots: interleave writes for memory-level parallelism
            pos1 = s1
            pos2 = s2
            while pos1 <= sieve_len && pos2 <= sieve_len
                sieve[pos1] -= logp
                sieve[pos2] -= logp
                pos1 += p
                pos2 += p
            end
            while pos1 <= sieve_len
                sieve[pos1] -= logp
                pos1 += p
            end
            while pos2 <= sieve_len
                sieve[pos2] -= logp
                pos2 += p
            end
        else
            # Single root (p | a)
            pos = s1
            while pos <= sieve_len
                sieve[pos] -= logp
                pos += p
            end
        end
    end
end

"""
Collect smooth candidates from sieve. Candidates are positions where the sieve
value underflowed (>= 0x80), indicating sufficient factorization over the factor base.
"""
function _siqs_collect!(poly::MPQSPolynomial{T}, ctx::MPQSContext,
                        sieve::Vector{UInt8}, starts1::Vector{Int}, starts2::Vector{Int},
                        relations::Vector{SmoothRelation},
                        partial_relations::Dict{Int, SmoothRelation},
                        M::Int, large_prime_bound::Int, dlp_bound::Int, dlp_bound_sq::Int,
                        tf_exponents::BitVector, tf_full_exp::Vector{Int32}) where {T<:Integer}
    a, b, c = poly.a, poly.b, poly.c
    sieve_len = length(sieve)

    # Vectorized sieve scanning: process 8 bytes at a time via reinterpret
    num_chunks = div(sieve_len, 8)
    body_len = num_chunks * 8

    if num_chunks > 0
        sieve_body = @view sieve[1:body_len]
        sieve_chunks = reinterpret(UInt64, sieve_body)

        @inbounds for j in 1:num_chunks
            chunk = sieve_chunks[j]
            # The bitmask trick: check if any of the 8 bytes have the high bit set
            if chunk & 0x8080808080808080 != 0
                for k in 1:8
                    idx = (j - 1) * 8 + k
                    if sieve[idx] >= 0x80
                        _process_candidate!(idx, a, b, c, M, ctx,
                                            large_prime_bound, dlp_bound, dlp_bound_sq,
                                            starts1, starts2, poly.a_factors,
                                            tf_exponents, tf_full_exp,
                                            relations, partial_relations)
                    end
                end
            end
        end
    end

    # Handle the tail (remaining 1 to 7 bytes that didn't fit in a UInt64)
    @inbounds for i in (body_len + 1):sieve_len
        if sieve[i] >= 0x80
            _process_candidate!(i, a, b, c, M, ctx,
                                large_prime_bound, dlp_bound, dlp_bound_sq,
                                starts1, starts2, poly.a_factors,
                                tf_exponents, tf_full_exp,
                                relations, partial_relations)
        end
    end
end

"""
Process a single sieve candidate at position `i`.
"""
@inline function _process_candidate!(i::Int, a::T, b::T, c::T, M::Int,
                             ctx::MPQSContext,
                             large_prime_bound::Int, dlp_bound::Int, dlp_bound_sq::Int,
                             starts1::Vector{Int}, starts2::Vector{Int},
                             a_factors::Vector{Int},
                             tf_exponents::BitVector, tf_full_exp::Vector{Int32},
                             relations::Vector{SmoothRelation},
                             partial_relations::Dict{Int, SmoothRelation}) where {T<:Integer}
    x = T(i - M - 1)
    # g(x) = Q(x)/a = a·x² + 2b·x + c, by Horner. Evaluating g directly keeps every
    # intermediate at g's own width — forming Q(x) = (ax+b)² - kn would need twice that.
    gx = (a * x + 2 * b) * x + c
    iszero(gx) && return
    ax_b = a * x + b

    relation = _trial_factor_guided(ax_b, gx, ctx.n_orig, ctx,
                                    large_prime_bound, dlp_bound, dlp_bound_sq,
                                    i, starts1, starts2,
                                    a_factors,
                                    tf_exponents, tf_full_exp)
    relation === nothing && return

    if relation.large_prime == 0 && relation.large_prime2 == 0
        # Fully smooth
        push!(relations, relation)
    elseif relation.large_prime2 == 0
        # Single large prime partial
        lp = relation.large_prime
        if haskey(partial_relations, lp)
            other = partial_relations[lp]
            combined = _combine_partials(relation, other, lp, ctx)
            if combined !== nothing
                if combined.large_prime2 == 0
                    push!(relations, combined)
                end
                # If combined still has 2 LPs, discard (too complex to chain)
            end
            delete!(partial_relations, lp)
        else
            partial_relations[lp] = relation
        end
    else
        # Double large prime partial — try to combine with existing single partials
        lp1, lp2 = relation.large_prime, relation.large_prime2
        if haskey(partial_relations, lp1)
            other = partial_relations[lp1]
            combined = _combine_partials(relation, other, lp1, ctx)
            delete!(partial_relations, lp1)
            if combined !== nothing
                if combined.large_prime2 == 0
                    # Fully resolved — push as full relation
                    push!(relations, combined)
                else
                    # One remaining LP — store as single-LP partial
                    remaining_lp = combined.large_prime2
                    if haskey(partial_relations, remaining_lp)
                        other2 = partial_relations[remaining_lp]
                        combined2 = _combine_partials(combined, other2, remaining_lp, ctx)
                        if combined2 !== nothing && combined2.large_prime2 == 0
                            push!(relations, combined2)
                        end
                        delete!(partial_relations, remaining_lp)
                    else
                        partial_relations[remaining_lp] = combined
                    end
                end
            end
        elseif haskey(partial_relations, lp2)
            other = partial_relations[lp2]
            combined = _combine_partials(relation, other, lp2, ctx)
            delete!(partial_relations, lp2)
            if combined !== nothing
                if combined.large_prime2 == 0
                    push!(relations, combined)
                else
                    remaining_lp = combined.large_prime2
                    if haskey(partial_relations, remaining_lp)
                        other2 = partial_relations[remaining_lp]
                        combined2 = _combine_partials(combined, other2, remaining_lp, ctx)
                        if combined2 !== nothing && combined2.large_prime2 == 0
                            push!(relations, combined2)
                        end
                        delete!(partial_relations, remaining_lp)
                    else
                        partial_relations[remaining_lp] = combined
                    end
                end
            end
        else
            # Store indexed by smaller LP for future matching
            partial_relations[lp1] = relation
        end
    end
end

"""
    mpqs_factor(n::Integer) -> BigInt

Factor `n` using the Self-Initializing Quadratic Sieve (SIQS variant of MPQS).
Uses constant sieve initialization, unclamped subtraction, small prime skipping,
and incremental Gray code root updates for performance.
Returns a non-trivial factor of `n`.

The polynomial arithmetic runs in the narrowest type that provably holds it: the
largest intermediate is Horner's `(a·x + 2b)·x` at roughly `M·√(2kn)`, so anything
that fits in 126 bits is sieved in `Int128` rather than `BigInt`. Only the mod-`n`
steps — combining partials and extracting the factor — need `n`'s full width.
"""
function mpqs_factor(n::Integer)
    nb = BigInt(n)
    k = _select_knuth_multiplier(nb)
    kn = BigInt(k) * nb
    fb_size_target, sieve_interval = _mpqs_select_params(nb)
    width = ndigits(isqrt(2 * kn), base=2) + ndigits(sieve_interval, base=2) + 4
    return width <= 126 ?
        _mpqs_factor(Int128, nb, k, kn, fb_size_target, sieve_interval) :
        _mpqs_factor(BigInt, nb, k, kn, fb_size_target, sieve_interval)
end

function _mpqs_factor(::Type{T}, n::BigInt, k::Int, kn::BigInt,
                      fb_size_target::Int, sieve_interval::Int)::BigInt where {T<:Integer}
    factor_base, sqrt_kn_mod, log_primes = _build_factor_base(kn, fb_size_target)
    actual_fb_size = length(factor_base)

    ctx = MPQSContext(kn, n, k, factor_base, actual_fb_size,
                      sqrt_kn_mod, log_primes, sieve_interval)

    relations = SmoothRelation[]
    partial_relations = Dict{Int, SmoothRelation}()
    used_a_sets = Set{Vector{Int}}()
    target_relations = actual_fb_size + 50

    M = sieve_interval
    sieve_len = 2 * M + 1

    # Preallocate buffers (reused across all polynomials)
    sieve = Vector{UInt8}(undef, sieve_len)
    starts1 = Vector{Int}(undef, actual_fb_size)
    starts2 = Vector{Int}(undef, actual_fb_size)
    offset1 = Vector{Int}(undef, actual_fb_size)
    offset2 = Vector{Int}(undef, actual_fb_size)

    # Preallocate trial factoring buffers (reused across all candidates)
    tf_exponents = falses(actual_fb_size + 1)
    tf_full_exp = zeros(Int32, actual_fb_size + 1)

    # Constant sieve init: candidates are detected by UInt8 underflow (>= 0x80).
    # log_init calibrated to match reference implementation threshold.
    # nbits ≈ log2(sqrt(2kn)), up_to = 1.5 tolerance factor
    nbits = ndigits(isqrt(2 * kn), base=2)
    logp_max = floor(Int, log2(Float64(factor_base[end])))
    up_to = 1.5
    log_init = UInt8(clamp(nbits - round(Int, up_to * logp_max), 1, 127))

    # Skip small primes in sieve (they hit too many positions relative to their
    # log contribution). They are still checked during trial factoring.
    # Ref: skip primes < 2^4 when nbits < 90, < 2^5 when 90-120, < 2^6 when > 120
    skip_limit = nbits > 120 ? 512 : (nbits > 90 ? 256 : (nbits > 78 ? 128 : 32))
    sieve_start_idx = 1
    while sieve_start_idx <= actual_fb_size && factor_base[sieve_start_idx] < skip_limit
        sieve_start_idx += 1
    end

    # Large prime bounds
    p_max = factor_base[end]
    large_prime_bound = (2 + (p_max >> 16)) * p_max * floor(Int, log2(Float64(p_max)))
    # Double large prime: accept remainder = p1 * p2 where both < dlp_bound
    dlp_bound = p_max * 100
    dlp_bound_sq = dlp_bound * dlp_bound

    max_a_values = 5000
    done = false

    # Preallocate B_delta arrays (reused across a-values)
    max_s = 10
    B_delta = [Vector{Int}(undef, actual_fb_size) for _ in 1:max_s]
    inv_a = Vector{Int}(undef, actual_fb_size)

    for _ in 1:max_a_values
        done && break

        result = _generate_siqs_a(T, ctx, used_a_sets)
        result === nothing && continue
        a, a_indices, B_comps = result
        s = length(a_indices)
        a_big = BigInt(a)   # only for the b² - kn computation, which overflows T

        # Precompute inv(a) mod p using factored form (avoids GMP BigInt mod)
        # a = prod(factor_base[idx] for idx in a_indices)
        @inbounds for j in 1:actual_fb_size
            p = factor_base[j]
            a_mod_p = 1
            for idx in a_indices
                if factor_base[idx] == p
                    a_mod_p = 0
                    break
                end
                a_mod_p = mod(a_mod_p * mod(factor_base[idx], p), p)
            end
            if a_mod_p == 0
                inv_a[j] = 0
            else
                inv_a[j] = invmod(a_mod_p, p)
            end
        end

        # Precompute root deltas for incremental Gray code b-switching
        # B_delta[v][j] = 2 * B_v mod p * inv_a[j] mod p
        for v in 1:s
            Bv = B_comps[v]
            delta = B_delta[v]
            @inbounds for j in 1:actual_fb_size
                p = factor_base[j]
                Bv_mod_p = Int(mod(Bv, p))
                delta[j] = mod(2 * Bv_mod_p * inv_a[j], p)
            end
        end

        # Initial b (all positive CRT signs)
        b = mod(sum(B_comps), a)
        if mod(BigInt(b) * BigInt(b), a_big) != mod(kn, a_big)
            b = a - b
        end
        c = _poly_c(T, b, kn, a_big)

        # Compute initial roots (once per a)
        _compute_siqs_roots!(offset1, offset2, b, c, inv_a,
                              sqrt_kn_mod, factor_base, actual_fb_size, M, a_indices)

        # First polynomial
        _siqs_sieve!(sieve, sieve_len, offset1, offset2, starts1, starts2,
                     factor_base, log_primes, actual_fb_size, sieve_start_idx, log_init)
        poly = MPQSPolynomial(a, b, c, a_indices)
        _siqs_collect!(poly, ctx, sieve, starts1, starts2,
                       relations, partial_relations, M, large_prime_bound,
                       dlp_bound, dlp_bound_sq,
                       tf_exponents, tf_full_exp)

        if length(relations) >= target_relations
            break
        end

        # Remaining b-values via Gray code incremental root update
        num_b = 1 << (s - 1)
        for i in 2:num_b
            gray_prev = (i - 2) ⊻ ((i - 2) >> 1)
            gray_curr = (i - 1) ⊻ ((i - 1) >> 1)
            flip_bit = trailing_zeros(gray_prev ⊻ gray_curr) + 1

            if (gray_curr >> (flip_bit - 1)) & 1 == 1
                b = mod(b - 2 * B_comps[flip_bit], a)
                dd = +1  # roots shift right
            else
                b = mod(b + 2 * B_comps[flip_bit], a)
                dd = -1  # roots shift left
            end

            # Incremental root update (pure Int arithmetic, no BigInt mod)
            delta = B_delta[flip_bit]
            @inbounds for j in 1:actual_fb_size
                inv_a[j] == 0 && continue
                p = factor_base[j]
                d = delta[j]
                if dd > 0
                    o1 = offset1[j] + d; if o1 >= p; o1 -= p; end
                    offset1[j] = o1
                    o2 = offset2[j] + d; if o2 >= p; o2 -= p; end
                    offset2[j] = o2
                else
                    o1 = offset1[j] - d; if o1 < 0; o1 += p; end
                    offset1[j] = o1
                    o2 = offset2[j] - d; if o2 < 0; o2 += p; end
                    offset2[j] = o2
                end
            end

            # Recompute roots for primes dividing a (~s primes)
            c = _poly_c(T, b, kn, a_big)
            for idx in a_indices
                p = factor_base[idx]
                b2_mod_p = mod(2 * Int(mod(b, p)), p)
                c_mod_p = Int(mod(c, p))
                if b2_mod_p == 0
                    offset1[idx] = -1; offset2[idx] = -1
                else
                    b_inv = invmod(b2_mod_p, p)
                    r = mod(-c_mod_p * b_inv, p)
                    o = mod(r + M, p)
                    offset1[idx] = o; offset2[idx] = o
                end
            end

            # Sieve and collect
            _siqs_sieve!(sieve, sieve_len, offset1, offset2, starts1, starts2,
                         factor_base, log_primes, actual_fb_size, sieve_start_idx, log_init)
            poly = MPQSPolynomial(a, b, c, a_indices)
            _siqs_collect!(poly, ctx, sieve, starts1, starts2,
                           relations, partial_relations, M, large_prime_bound,
                           dlp_bound, dlp_bound_sq,
                           tf_exponents, tf_full_exp)

            if length(relations) >= target_relations
                done = true
                break
            end
        end
    end

    if length(relations) < actual_fb_size + 1
        error("failed to factor $n: insufficient smooth relations ($(length(relations)) found, need $(actual_fb_size + 1))")
    end

    # GF(2) elimination
    parity_vectors = [r.exponents for r in relations]
    dependencies = _gf2_eliminate(parity_vectors, actual_fb_size)

    # Try each dependency to find a non-trivial factor
    for dep in dependencies
        result = _extract_factor(n, kn, k, dep, relations, factor_base)
        if result !== nothing
            return result
        end
    end

    error("failed to factor $n")
end
