-- Prove2me | solution 1 for measurable_positivePart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:19:01.63653+00:00
-- url     : https://prove2.me/submissions/b0c17ab4-33b9-460d-b691-01dc7b9cfb96

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem solution (hX : Measurable X) : Measurable (positivePart X) := by
  unfold positivePart
  exact (continuous_id.max continuous_const).measurable.comp hX
end PositiveNegativeParts
