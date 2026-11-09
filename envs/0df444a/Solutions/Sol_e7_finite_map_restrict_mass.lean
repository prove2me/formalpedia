-- Prove2me | solution 1 for e7_finite_map_restrict_mass
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:15:44.11843+00:00
-- url     : https://prove2.me/submissions/d2b31255-4f4a-4e1a-a6ab-a6fef249534c

import Mathlib

open MeasureTheory

theorem solution {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (g : Ω → E) (hg : Measurable g)
    (μ : MeasureTheory.FiniteMeasure E)
    (hμ : μ.toMeasure = Measure.map g (P.restrict A)) :
    μ.mass = P A := by
  have h : (μ : Measure E) Set.univ = P A := by
    rw [hμ, Measure.map_apply hg MeasurableSet.univ]
    simp
  rw [MeasureTheory.FiniteMeasure.ennreal_mass]
  exact h
