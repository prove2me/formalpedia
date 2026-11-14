-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_adaptive_fresh_observed_general
-- name    : CountingLLL.ReciprocalTest.adaptive_fresh_observed_general
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:39:42.258855+00:00
-- url     : https://prove2.me/theorems/36a4c5eb-e3b9-4794-aaac-db5b36e73c8d
-- title:
--   Deferred decisions with adaptive finite reveals and mixed coordinate laws
-- statement:
--   Let a nonanticipating rule observe a finite random set of an independent countable-valued array and select an unrevealed coordinate. For an observed event $E$, if the selected coordinate event has probability $p$ on $E$, then the probability of $E$ together with that event is $p\Pr(E)$. The laws and events may vary by coordinate. This applies to oracle bits, fair bits, and finite-uniform tests after embedding their values in a common countable space.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.adaptive_fresh_observed_general {ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (p : ℝ≥0∞)
    (revealed : (ι → α) → Finset ι) (next : (ι → α) → ι)
    (hfresh : ∀ ω, next ω ∉ revealed ω)
    (E : Set (ι → α))
    (hsame : ∀ ω, ω ∈ E → κ (next ω) (A (next ω)) = p)
    (hlocal : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      ((revealed ω = S ∧ next ω = a) ↔ (revealed ω' = S ∧ next ω' = a)))
    (hobserved : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      (revealed ω = S ∧ next ω = a) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} =
      (Measure.infinitePi κ) E * p := by sorry
