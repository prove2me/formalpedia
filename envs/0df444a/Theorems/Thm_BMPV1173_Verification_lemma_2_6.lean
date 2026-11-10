-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_2_6
-- name    : BMPV1173.Verification.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:06:39.775496+00:00
-- url     : https://prove2.me/theorems/bd1cb4a3-2341-4b51-8f16-82444020277a
-- title:
--   Lemma 2.6 — successive marked positions
-- statement:
--   For an ordered universe of length $M$, let a procedure repeatedly find the next marked coordinate after its cursor, update its predicate using the discovered history, and stop after $K$ marks or after discovering that no later mark exists. Passed coordinates need not be revisited. Suppose its predicate tests cost at most $q$ queries, after amplification to the required inverse-polynomial accuracy. There is a single quantum procedure that outputs the complete cursor trace, including the no-more-marks termination when relevant, with arbitrarily high inverse-polynomial success and completion guarantee, within
--   $$\widetilde O\!\left(q\sqrt{(M+1)(K+1)}\right)$$
--   queries. The source has constant $q$. The ambient parameter bounds $M,K$ polynomially, including $M=0$ and $K=0$. Tests and the search are chosen before the unknown input; their success and running time use the actual Born law. Tests and the resulting search use persistent quantum state across partial observations, rather than resetting after a full-register measurement.
--
--   Differences from the source:
--   - encoding: polynomial-size parameters and inverse-polynomial subroutine error → fixed polynomial envelope and an existential required accuracy exponent before all instances; reason: this makes the section standing convention explicit; constants depend only on fixed envelopes and requested error exponents
--   - encoding: the successive-search procedure with a changing predicate → the recursively computed increasing cursor trace and a joint correct-output/completion probability; reason: the history determines the next predicate; the termination search is retained, and an O(1) predicate cost is exposed as q
--   - generalization: O(1) queries per predicate evaluation → a supplied bound q with the total resource expression multiplied by q; reason: every fixed constant predicate cost is an instance; the same query simulation also covers nonconstant q
--   - encoding: quantum tests with intermediate measurements and stopping flags → finite checkpoint programs with persistent quantum registers, partial projective observations, and unnormalized branch Born probabilities; reason: a checkpoint preserves all unobserved amplitudes; finite ancillas encode general measurements; joint completion and correctness retain actual query costs without replacing them by expectations
--   - encoding: entry-oracle calls and query-free stopping → an Option query address with none returning zero in the stopping model; reason: on nonempty input domains the dummy call is simulated by one original XOR query using a plus-state target; it also permits a normalized zero-query computation on an empty input domain
--   - generalization: the section convention that index sets have polynomial size in the ambient input parameter → an arbitrary finite input-oracle address type, with polynomial bounds on the candidate and resource parameters explicitly listed in the theorem; reason: the search bounds count entry queries and depend on candidate sizes and subroutine costs, not the number of input-oracle addresses; polynomial-size source oracles are included
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 2.6, printed p.15 = PDF p.15.

import Definitions.Def_BMPV1173_Verification_SearchTasks

namespace BMPV1173.Verification

/-- Successive marked positions, Lemma 2.6, p.15. All changing predicate
programs are fixed before the oracle input; the correct trace includes the
end search if fewer than K marks exist. Constant predicate query cost q is explicit. -/
theorem lemma_2_6 (c : ℝ) (hc : 0 < c) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (C : ℝ) (k e : ℕ), 0 < C ∧ ∀ (n M K q : ℕ),
    2 ≤ n → M ≤ n^b → K ≤ n^b → 1 ≤ q →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ test : List (Fin M) → Fin M → StoppingQueryAlg ι Bool,
    ∃ A : StoppingQueryAlg ι (List (Fin M)),
    ∀ (x : ι → Bool) (f : List (Fin M) → Fin M → Bool),
      (∀ hist j, hist.length ≤ K →
        boundedStoppingProb (test hist j) x (fun _ => True) q = 1 ∧
        1-(n : ℝ)^(-(e : ℝ)) ≤ (test hist j).outProb x (f hist j)) →
      1-(n : ℝ)^(-c) ≤ boundedStoppingProb A x
        (fun ans => ans = successiveTrace f K [])
        (C*q*Real.sqrt (((M : ℝ)+1)*((K : ℝ)+1))*(1+Real.log (n : ℝ))^k) := by sorry

end BMPV1173.Verification
