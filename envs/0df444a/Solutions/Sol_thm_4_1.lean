-- Prove2me | solution 1 for thm_4_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:17.137126+00:00
-- url     : https://prove2.me/submissions/7582b07f-c149-43ae-b824-300488d35cf3

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_2_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic


theorem solution {Ω : Type _} [MeasurableSpace Ω] (A : Set Ω) :
    Measurable (Set.indicator A (fun _ => (1 : ℝ))) ↔ MeasurableSet A := by
  constructor
  · intro h
    have : A = (Set.indicator A (fun _ => (1 : ℝ))) ⁻¹' {1} := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [this]
    exact h (measurableSet_singleton 1)
  · intro h
    exact measurable_const.indicator h

