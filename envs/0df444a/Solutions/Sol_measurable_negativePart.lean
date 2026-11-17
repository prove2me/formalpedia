-- Prove2me | solution 1 for measurable_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:23:24.89123+00:00
-- url     : https://prove2.me/submissions/28a2ff0a-df8a-4ff7-a4f3-49a6d067edad

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Theorems.Thm_measurable_positivePart
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem solution (hX : Measurable X) : Measurable (negativePart X) := by
  unfold negativePart
  exact ((continuous_id.min continuous_const).neg).measurable.comp hX
end PositiveNegativeParts
