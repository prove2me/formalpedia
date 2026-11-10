-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_2_9
-- name    : BMPV1173.Verification.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:05:35.200292+00:00
-- url     : https://prove2.me/theorems/6c3c263c-a407-4870-9995-457bab1d0a8c
-- title:
--   Lemma 2.9 — search with variable stopping times
-- statement:
--   Each of $n$ candidate tests returns its correct Boolean answer within $q_j\ge1$ queries with sufficiently high inverse-polynomial probability, and may have a measurement-dependent stopping time. Given only a known bound
--   $$Q\ge\sqrt{\sum_{j=1}^n q_j^2},$$
--   one quantum search finds an accepting candidate or correctly reports that none exists with arbitrarily high inverse-polynomial probability in $\widetilde O(Q)$ queries. The resulting search is truncated at that budget on every input. Its program is chosen before the individual $q_j$, the unknown input and the correct answer vector; those bounds are not program input. The statement continues onto printed/PDF p.16. Tests and the resulting search use persistent quantum state across partial observations, rather than resetting after a full-register measurement.
--
--   Differences from the source:
--   - encoding: polynomial-size parameters and inverse-polynomial subroutine error → fixed polynomial envelope and an existential required accuracy exponent before all instances; reason: this makes the section standing convention explicit; constants depend only on fixed envelopes and requested error exponents
--   - encoding: variable stopping times and high probability → persistent-state measured checkpoint programs with a joint completion/correctness law and probability-one completion within the final truncated-search budget; reason: partial observations retain the remaining quantum state; Q is known whereas the individual bounds follow the algorithm quantifier; probability-one completion in a finite tree is a worst-case bound on positive-probability transcripts
--   - encoding: quantum tests with intermediate measurements and stopping flags → finite checkpoint programs with persistent quantum registers, partial projective observations, and unnormalized branch Born probabilities; reason: a checkpoint preserves all unobserved amplitudes; finite ancillas encode general measurements; joint completion and correctness retain actual query costs without replacing them by expectations
--   - encoding: entry-oracle calls and query-free stopping → an Option query address with none returning zero in the stopping model; reason: on nonempty input domains the dummy call is simulated by one original XOR query using a plus-state target; it also permits a normalized zero-query computation on an empty input domain
--   - generalization: the section convention that index sets have polynomial size in the ambient input parameter → an arbitrary finite input-oracle address type, with polynomial bounds on the candidate and resource parameters explicitly listed in the theorem; reason: the search bounds count entry queries and depend on candidate sizes and subroutine costs, not the number of input-oracle addresses; polynomial-size source oracles are included
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 2.9, printed p.15 = PDF p.15; statement continues on p.16.

import Definitions.Def_BMPV1173_Verification_Resources

namespace BMPV1173.Verification

open scoped BigOperators

/-- Measurement-dependent stopping, Lemma 2.9, pp.15–16. The known Q bound
is supplied; the individual q_j are never supplied to the resulting search. -/
theorem lemma_2_9 (c : ℝ) (hc : 0 < c) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (C : ℝ) (k e : ℕ), 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ Q : ℝ, 1 ≤ Q → Q ≤ (n : ℝ)^b →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ test : Fin n → StoppingQueryAlg ι Bool,
    ∃ A : StoppingQueryAlg ι (Option (Fin n)),
      (∀ x, boundedStoppingProb A x (fun _ => True) (C*Q*(1+Real.log (n : ℝ))^k) = 1) ∧
      ∀ (x : ι → Bool) (f : Fin n → Bool) (q : Fin n → ℝ),
        (∀ j, 1 ≤ q j) → Real.sqrt (∑ j, (q j)^2) ≤ Q →
        (∀ j, 1-(n : ℝ)^(-(e : ℝ)) ≤
          boundedStoppingProb (test j) x (fun ans => ans = f j) (q j)) →
        1-(n : ℝ)^(-c) ≤ boundedStoppingProb A x (SearchAnswer f)
          (C*Q*(1+Real.log (n : ℝ))^k) := by sorry

end BMPV1173.Verification
