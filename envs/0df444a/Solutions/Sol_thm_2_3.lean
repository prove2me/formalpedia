-- Prove2me | solution 1 for thm_2_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:11.254888+00:00
-- url     : https://prove2.me/submissions/94a0403c-525e-4b81-96ff-0a89f772d1a9

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_5_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory Set


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∪ B) ≤ μ A + μ B := by
  exact measure_union_le A B

