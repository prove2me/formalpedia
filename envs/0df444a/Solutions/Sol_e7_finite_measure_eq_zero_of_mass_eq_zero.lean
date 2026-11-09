-- Prove2me | solution 1 for e7_finite_measure_eq_zero_of_mass_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:03:59.645202+00:00
-- url     : https://prove2.me/submissions/a11b978b-6029-4d9a-a821-3c5055264b25

import Mathlib

open MeasureTheory

theorem solution {E : Type*} [MeasurableSpace E]
    (μ : MeasureTheory.FiniteMeasure E) (hmass : μ.mass = 0) :
    μ.toMeasure = 0 := by
  have h : μ.toMeasure Set.univ = 0 := by
    simpa [MeasureTheory.FiniteMeasure.mass] using hmass
  exact MeasureTheory.Measure.measure_univ_eq_zero.mp h
