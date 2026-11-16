-- Prove2me | solution 1 for thm_5_10
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:48.272203+00:00
-- url     : https://prove2.me/submissions/6311e9d0-99bb-40ce-b804-9a9fea4b18d3

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology


/-- ## Theorem 5.10 Borel's zero-one law
for independent measurable events in a probability space,
the probability of occurring infinitely often is
completely determined by whether the probability series
diverges or converges.
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P) :
    P (limsup A atTop) = if (∑' n, P (A n)) = ∞ then 1 else 0 := by
  split_ifs with h
  · exact ProbabilityTheory.measure_limsup_eq_one h_meas h_indep h
  · exact MeasureTheory.measure_limsup_atTop_eq_zero h

