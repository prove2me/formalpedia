-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_A_1
-- name    : EqualSubsetSum.Faster.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:24:19.725049+00:00
-- url     : https://prove2.me/theorems/88323b99-b7ea-407f-9a1f-ba5a1893fe98
-- title:
--   Lemma A.1 — bit-length reduction in O(n²m + poly(n)) on every execution
-- statement:
--   Let $n\ge1$ and $m\le 2^n$. There is a randomized procedure that receives $n$ integers of at most $m$ bits each and uses $O(n^2m+\mathrm{poly}(n))$ bit operations on every execution. It gives up with probability $2^{-\Omega(n)}$, and otherwise it produces $n+O(\log n)$ nonnegative integers of $O(n)$ bits. Whenever it produces an instance, every solution of the input extends to a solution of that instance. With probability $1-2^{-\Omega(n)}$, conditional on producing an instance, every solution of that instance restricts to a nonzero solution of the input.
--
--   In Lean: one program and constants $C,K,B,c>0,C'$; output $[0]$ (gives up) or $1,\tilde x_1,\dots,\tilde x_{n'}$ (an instance); cost $\le C(n^2m+(n+1)^K)$ on every tape; $\Pr[\text{give up}]\le C'2^{-cn}$; and $\Pr[\text{produce }\tilde x\text{ with a solution whose restriction is not a solution of }x]\le C'2^{-cn}\cdot\Pr[\text{produce}]$.
--
--   Differences from the source:
--   - reading: a randomized algorithm, its bit operations and its executions → a program of the published log-cost randomized RAM SubsetSumPartialMatch_SubsetSum_RAM, its charged cost, and each random tape; reason: the paper's cost model (§2.1: bit operations including arithmetic, memory addressing, sorting, random-bit generation) read as that machine
--   - encoding: receives n integers of at most m bits each → input words n, x₁, …, xₙ with maxBits x ≤ m; m is not an input word; reason: m is a parameter of the statement, not of the input
--   - encoding: O(n²m + poly(n)) on every execution → C·(n²m + (n + 1)^K) on every tape; reason: explicit O-notation with constants fixed before the input
--   - encoding: n + O(log n) nonnegative integers of O(n) bits → n' integers with n ≤ n' ≤ n + B(⌊log₂ n⌋ + 1), each 0 ≤ x̃ᵢ < 2^{B n}; reason: explicit O-notation; n' ≥ n because solutions of x extend to x̃
--   - encoding: every solution of the input extends to a solution of the instance; a solution restricts to one of the input → the extension's first n coordinates equal the given solution; restriction = first n coordinates; reason: the paper's construction appends auxiliary weights after the n reduced ones
--   - encoding: gives up with probability 2^{−Ω(n)}; with probability 1 − 2^{−Ω(n)} conditional on producing an instance → Pr[output [0]] ≤ C'2^{−cn}; Pr[produced ∧ bad] ≤ C'2^{−cn}·Pr[produced]; reason: explicit Ω; the conditional probability written without division
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 48, Lemma A.1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_EqualSubsetSum_Faster_Problem

namespace EqualSubsetSum.Faster

open SubsetSumPartialMatch.SubsetSum

/-- Lemma A.1 (p. 48). One program and constants `C, K, B, c > 0, C'` such that for every `n ≥ 1`,
every `m ≤ 2^n` and every `x : Fin n → ℤ` whose entries have at most `m` bits, on input words
`n, x₁, …, xₙ`: on every tape it halts within `C (n² m + (n + 1)^K)` bit operations, and either
gives up (output `[0]`) or produces (output `1 :: x̃`) an instance `x̃` of `n' ≤ n + B(log₂ n + 1)`
nonnegative integers below `2^{B n}`, `n' ≥ n`, to which every solution of `x` extends (the first
`n` coordinates of the extension are the given solution); it gives up with probability at most
`C' 2^{-c n}`; and the probability of producing an instance with a solution whose restriction
to the first `n` coordinates is not a (nonzero) solution of `x` is at most `C' 2^{-c n}` times
the probability of producing an instance. -/
theorem lemma_A_1 :
    ∃ P : Program, ∃ C : ℝ, ∃ K B : ℕ, ∃ c C' : ℝ, 0 < c ∧
      ∀ (n m : ℕ) (x : Fin n → ℤ), 1 ≤ n → m ≤ 2 ^ n → maxBits x ≤ m →
        (∀ ω : ℕ → Bool, CostWithin P ω (instanceWords x) (C * ((n : ℝ) ^ 2 * m + ((n : ℝ) + 1) ^ K))) ∧
        (∀ ω : ℕ → Bool, ∃ out, Outputs P ω (instanceWords x) out ∧
          (out = failureWord ∨
            ∃ (n' : ℕ) (h : n ≤ n') (xt : Fin n' → ℤ), out = 1 :: List.ofFn xt ∧
              n' ≤ n + B * (Nat.log 2 n + 1) ∧
              (∀ i, 0 ≤ xt i ∧ xt i < 2 ^ (B * n)) ∧
              ∀ d, IsSolution x d → ∃ d' : Fin n' → ℤ, IsSolution xt d' ∧
                ∀ i : Fin n, d' (Fin.castLE h i) = d i)) ∧
        failProb P (instanceWords x) ≤ ENNReal.ofReal (C' * (2 : ℝ) ^ (-(c * n))) ∧
        tapeMeasure {ω | ∃ (n' : ℕ) (h : n ≤ n') (xt : Fin n' → ℤ),
            Outputs P ω (instanceWords x) (1 :: List.ofFn xt) ∧
            ∃ d' : Fin n' → ℤ, IsSolution xt d' ∧ ¬ IsSolution x (fun i => d' (Fin.castLE h i))}
          ≤ ENNReal.ofReal (C' * (2 : ℝ) ^ (-(c * n))) *
            tapeMeasure {ω | ∃ out, Outputs P ω (instanceWords x) out ∧ out ≠ failureWord} := by sorry

end EqualSubsetSum.Faster
