-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_theorem_4_1
-- name    : EqualSubsetSum.Faster.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:24:20.099285+00:00
-- url     : https://prove2.me/theorems/b1951015-ce18-4d8f-821d-d144d5f15802
-- title:
--   Theorem 4.1 — arithmetic procedure on p ∈ [.2015, .2239380256] in poly(n+m)·2^{(.7336065+ε)n}
-- statement:
--   For every fixed $\varepsilon>0$ there is a randomized algorithm (a program $P$ of the log-cost randomized RAM) that receives $x\in\mathbb Z^n$ and an integer $k$ with
--   $$p=k/n\in[.2015,\ .2239380256]$$
--   and has the following properties. On every execution it uses at most $\mathrm{poly}(n+m)\,2^{(.7336065+\varepsilon)n}$ bit operations and returns only solutions for $x$ (or failure). If the guess $k$ is correct, it fails with probability $2^{-\Omega(n)}$.
--
--   In Lean: `IsGuessProcedure P [p₀, p₁] (fun _ => c★ + ε)`.
--
--   Differences from the source:
--   - reading: a randomized algorithm, its bit operations and its executions → a program of the published log-cost randomized RAM SubsetSumPartialMatch_SubsetSum_RAM, its charged cost, and each random tape; reason: the paper's cost model (§2.1: bit operations including arithmetic, memory addressing, sorting, random-bit generation) read as that machine
--   - encoding: receives x ∈ ℤⁿ and an integer k → input words n, k, x₁, …, xₙ with k : ℕ, n ≥ 1 and k < n; reason: k/n requires n ≥ 1; guesses are k ∈ {0, …, n − 1} (§3); the stated range already forces 0 ≤ k < n
--   - encoding: poly(n + m) (a fixed polynomial in n + m) → C·(n + m + 1)^K with constants C, K fixed before the input, m = maxBits x; reason: explicit form of the paper's O*-notation (§1.1)
--   - encoding: failure probability 2^{−Ω(n)} → probability of the output [0] at most C'·2^{−c n} with c > 0, C' fixed, for every n; reason: explicit form of Ω(n); a bound for all n is the same as one for large n up to the constant C'
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 21, Theorem 4.1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_EqualSubsetSum_Faster_Problem
import Definitions.Def_EqualSubsetSum_Faster_Exponents

namespace EqualSubsetSum.Faster

open SubsetSumPartialMatch.SubsetSum

/-- Theorem 4.1 (p. 21). For every fixed `ε > 0` there is a program that receives `x ∈ ℤⁿ` and a
guess `k` with `p = k/n ∈ [.2015, .2239380256]`, halts on every tape with an output that is
failure or a solution for `x` within `poly(n + m) 2^{(.7336065 + ε) n}` bit operations, and
fails with probability `2^{-Ω(n)}` when the guess is correct. -/
theorem theorem_4_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Program, IsGuessProcedure P (Set.Icc p0 p1) (fun _ => cStar + ε) := by sorry

end EqualSubsetSum.Faster
