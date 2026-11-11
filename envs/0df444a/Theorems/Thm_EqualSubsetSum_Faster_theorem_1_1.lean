-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_theorem_1_1
-- name    : EqualSubsetSum.Faster.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:24:11.410765+00:00
-- url     : https://prove2.me/theorems/dab339c9-af75-4908-8f31-c4fb14a53f00
-- title:
--   Theorem 1.1 — Equal-Subset-Sum in O*(1.662791^n) bit operations on every execution, failure probability 2^{−Ω(n)}
-- statement:
--   There is one program $P$ of the log-cost randomized RAM and constants $C,K,c>0,C'$, fixed before the instance, such that for every $n\ge0$ and every $x\in\mathbb Z^n$, with $m$ the maximum bit length of the $|x_i|$, on input words $n,x_1,\dots,x_n$:
--
--   1. on every tape $P$ halts and its output is either failure $[0]$ or $1,d_1,\dots,d_n$ for a nonzero $d\in\{-1,0,1\}^n$ with $d\cdot x=0$;
--   2. on every tape it halts within $C\,(n+m+1)^K\,1.662791^n$ charged bit operations, i.e. $O^*(1.662791^n)$;
--   3. if $m\le 2^n$, on every tape it halts within
--   $$C\big(1.662791^n\,(n+1)^K+n^2m\big);$$
--   4. if such a vector $d$ exists, the probability that $P$ outputs failure is at most $C'2^{-cn}$.
--
--   This is the paper's main result, improving the base $5/3$ of the previous best algorithm.
--
--   Differences from the source:
--   - reading: a uniform randomized algorithm, its bit cost and its executions → one program of the published log-cost randomized RAM SubsetSumPartialMatch_SubsetSum_RAM, its charged cost, and each random tape; reason: the paper's cost model (§2.1: bit operations including arithmetic, memory addressing, sorting, random-bit generation; fair random bits) read as that machine; 'uniform' = one fixed program for all n
--   - encoding: the input x₁, …, xₙ in binary; output a vector d or failure → input words n, x₁, …, xₙ (one word per integer); output [0] or 1, d₁, …, dₙ; reason: one machine word per integer; validity is checked on the decoded d
--   - encoding: O*(1.662791^n), O* hiding a fixed polynomial in n + m → C·(n + m + 1)^K·1.662791^n with m = maxBits x; reason: explicit O*-notation (§1.1)
--   - encoding: O(1.662791^n poly(n) + n²m) when m ≤ 2^n → C·(1.662791^n·(n + 1)^K + n²·m) when maxBits x ≤ 2^n; reason: explicit O- and poly-notation
--   - encoding: failure probability 2^{−Ω(n)} → probability of the output [0] at most C'·2^{−c n} with c > 0, C' fixed, for every n; reason: explicit form of Ω(n); a bound for all n is the same as one for large n up to the constant C'
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_EqualSubsetSum_Faster_Problem

namespace EqualSubsetSum.Faster

open SubsetSumPartialMatch.SubsetSum

/-- Theorem 1.1 (p. 3). One program `P` of the log-cost randomized RAM, and constants
`C`, `K`, `c > 0`, `C'` fixed before the instance, such that for every `n` and every
`x : Fin n → ℤ`, with `m = maxBits x`, on input words `n, x₁, …, xₙ`:
(i) on every tape `P` halts with output failure `[0]` or `1 :: d` for a solution `d` of `x`;
(ii) on every tape it halts within `C (n + m + 1)^K · 1.662791^n` bit operations;
(iii) if `m ≤ 2^n`, on every tape it halts within `C (1.662791^n (n + 1)^K + n² m)`;
(iv) if `x` has a solution, it outputs failure with probability at most `C' 2^{-c n}`. -/
theorem theorem_1_1 :
    ∃ P : Program, ∃ C : ℝ, ∃ K : ℕ, ∃ c C' : ℝ, 0 < c ∧
      ∀ (n : ℕ) (x : Fin n → ℤ),
        (∀ ω : ℕ → Bool, ∃ out, Outputs P ω (instanceWords x) out ∧ ValidOutput x out) ∧
        (∀ ω : ℕ → Bool, CostWithin P ω (instanceWords x)
            (C * ((n : ℝ) + maxBits x + 1) ^ K * (1662791 / 1000000 : ℝ) ^ n)) ∧
        (maxBits x ≤ 2 ^ n → ∀ ω : ℕ → Bool, CostWithin P ω (instanceWords x)
            (C * ((1662791 / 1000000 : ℝ) ^ n * ((n : ℝ) + 1) ^ K + (n : ℝ) ^ 2 * maxBits x))) ∧
        ((∃ d, IsSolution x d) →
            failProb P (instanceWords x) ≤ ENNReal.ofReal (C' * (2 : ℝ) ^ (-(c * n)))) := by sorry

end EqualSubsetSum.Faster
