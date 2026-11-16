-- Prove2me | solution 1 for thm_5_9
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:47.644508+00:00
-- url     : https://prove2.me/submissions/76041b25-f4fd-45c7-92f9-59538e53921e

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology


/--  ## Theorem 5.9 Borel-Cantelli Lemma 2
for independent measurable events in a probability
space, divergence of the probability series forces the limsup event to have
probability one.

We keep the statement at the event level and use Mathlib's
`ProbabilityTheory.measure_limsup_eq_one` for the proof.
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P)
    (h_series : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 := by
  exact ProbabilityTheory.measure_limsup_eq_one h_meas h_indep h_series

