-- Prove2me | solution 1 for thm_2_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:12.066794+00:00
-- url     : https://prove2.me/submissions/bddf213e-7c18-46e8-985e-7f3fb7c0bae6

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_5_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory Set


/-- Exported theorem for monotonicity of measures. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  exact measure_mono hAB

