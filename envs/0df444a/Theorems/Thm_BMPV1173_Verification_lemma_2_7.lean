-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_2_7
-- name    : BMPV1173.Verification.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:05:25.10942+00:00
-- url     : https://prove2.me/theorems/84294cae-b31b-48ec-a257-13ccc7c2a485
-- title:
--   Lemma 2.7 — search with unknown completion costs
-- statement:
--   For each candidate $j$, a supplied test with allowance $u\ge1$ reports Unfinished below its unknown positive integer threshold $\tau_j$ and returns the correct Boolean answer at or above that threshold. Its actual query cost is $\widetilde O(u)$ and its error can be made inverse polynomial. For every specified $c>0$, one variable-time search finds an accepting candidate, or correctly reports that none exists, and completes with probability at least $1-n^{-c}$ within
--   $$\widetilde O\!\left(\sqrt{\sum_j\tau_j^2}\right)$$
--   queries. The program is chosen from the test programs and a fixed polynomial envelope before the unknown input, answers and thresholds. Neither the thresholds nor their sum of squares is supplied to it. The empty candidate family returns no candidate. Tests and the resulting search use persistent quantum state across partial observations, rather than resetting after a full-register measurement.
--
--   Differences from the source:
--   - encoding: polynomial-size parameters and inverse-polynomial subroutine error → fixed polynomial envelope and an existential required accuracy exponent before all instances; reason: this makes the section standing convention explicit; constants depend only on fixed envelopes and requested error exponents
--   - encoding: success and completion within the stated bound → joint Born probability of an accepting witness or a correct none answer and completion within that budget; reason: this retains the running-time guarantee instead of replacing it by expected cost; fixed test overhead is absorbed in a logarithmic exponent
--   - encoding: quantum tests with intermediate measurements and stopping flags → finite checkpoint programs with persistent quantum registers, partial projective observations, and unnormalized branch Born probabilities; reason: a checkpoint preserves all unobserved amplitudes; finite ancillas encode general measurements; joint completion and correctness retain actual query costs without replacing them by expectations
--   - encoding: entry-oracle calls and query-free stopping → an Option query address with none returning zero in the stopping model; reason: on nonempty input domains the dummy call is simulated by one original XOR query using a plus-state target; it also permits a normalized zero-query computation on an empty input domain
--   - generalization: allowance tests valid for every integer allowance u ≥ 1 → test validity required only for allowances up to the fixed polynomial envelope n^b; reason: all completion thresholds lie within that envelope and the search need not use larger allowances; every source test satisfies this restricted validity premise
--   - generalization: the section convention that index sets have polynomial size in the ambient input parameter → an arbitrary finite input-oracle address type, with polynomial bounds on the candidate and resource parameters explicitly listed in the theorem; reason: the search bounds count entry queries and depend on candidate sizes and subroutine costs, not the number of input-oracle addresses; polynomial-size source oracles are included
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 2.7, printed p.15 = PDF p.15.

import Definitions.Def_BMPV1173_Verification_Resources

namespace BMPV1173.Verification

open scoped BigOperators

/-- Unknown completion costs, Lemma 2.7, p.15. Only the fixed polynomial
envelope and test programs are known; τ and their square sum are quantified
after the search program has been chosen. -/
theorem lemma_2_7 (c : ℝ) (hc : 0 < c) (b h : ℕ) (hb : 1 ≤ b) :
    ∃ (C : ℝ) (k e : ℕ), 0 < C ∧
    ∀ (n m : ℕ), 2 ≤ n → m ≤ n^b →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ test : Fin m → ℕ → StoppingQueryAlg ι (Option Bool),
    ∃ A : StoppingQueryAlg ι (Option (Fin m)),
    ∀ (x : ι → Bool) (f : Fin m → Bool) (τ : Fin m → ℕ),
      (∀ j, 1 ≤ τ j ∧ τ j ≤ n^b) →
      StoppingAllowanceValidAt test x f τ ((n : ℝ)^(-(e : ℝ)))
        ((1+Real.log (n : ℝ))^h) (n^b) →
      1-(n : ℝ)^(-c) ≤ boundedStoppingProb A x (SearchAnswer f)
        (C * Real.sqrt (∑ j, (τ j : ℝ)^2) * (1+Real.log (n : ℝ))^k) := by sorry

end BMPV1173.Verification
