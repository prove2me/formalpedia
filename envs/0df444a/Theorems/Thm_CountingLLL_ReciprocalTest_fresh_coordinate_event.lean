-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_fresh_coordinate_event
-- name    : CountingLLL.ReciprocalTest.fresh_coordinate_event
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:33:53.735385+00:00
-- url     : https://prove2.me/theorems/feb902a8-1f1a-459c-91dd-c565ce9a7f5e
-- title:
--   Fresh independent bit after any finite set of reveals
-- statement:
--   Consider a countable family of independent Boolean coordinates, possibly with different one-coordinate laws. If an event depends only on a finite set $S$ of coordinates and $a\notin S$, then $$\Pr(E\cap\{X_a=1\})=\Pr(E)\Pr(X_a=1).$$ This supports deferred decisions for interleaved oracle and fair-bit reveals in the reciprocal-test machine.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.fresh_coordinate_event {ι : Type*} [Countable ι] [DecidableEq ι]
    (κ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (κ i)]
    (S : Finset ι) (a : ι) (ha : a ∉ S) (E : Set (ι → Bool))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω a = true} =
      (Measure.infinitePi κ) E * κ a {true} := by sorry
