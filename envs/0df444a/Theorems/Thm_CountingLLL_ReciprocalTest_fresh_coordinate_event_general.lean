-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_fresh_coordinate_event_general
-- name    : CountingLLL.ReciprocalTest.fresh_coordinate_event_general
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:39:41.602945+00:00
-- url     : https://prove2.me/theorems/145b3669-7288-4b39-a2d7-b6489ac4d50a
-- title:
--   Fresh countable-valued coordinate after finite reveals
-- statement:
--   In a countable independent array of countable-valued coordinates, any event determined by a finite set $S$ of coordinates is independent of an event on a fresh coordinate outside $S$. The coordinate laws and coordinate events may differ.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.fresh_coordinate_event_general {ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (S : Finset ι) (a : ι) (ha : a ∉ S) (E : Set (ι → α))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω a ∈ A a} =
      (Measure.infinitePi κ) E * κ a (A a) := by sorry
