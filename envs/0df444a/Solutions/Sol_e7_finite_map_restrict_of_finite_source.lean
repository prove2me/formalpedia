-- Prove2me | solution 1 for e7_finite_map_restrict_of_finite_source
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:15:39.787686+00:00
-- url     : https://prove2.me/submissions/1dfc01c1-0137-4b6b-8b6f-09e8365440af

import Mathlib

open MeasureTheory

theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (A : Set Ω) (g : Ω → E) :
    ∃ μ : MeasureTheory.FiniteMeasure E,
      μ.toMeasure = Measure.map g (P.restrict A) := by
  refine ⟨⟨Measure.map g (P.restrict A), ?_⟩, rfl⟩
  infer_instance
