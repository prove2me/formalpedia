-- Prove2me | solution 1 for positivePart_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:07.382912+00:00
-- url     : https://prove2.me/submissions/cf748af6-812b-4c1f-9fc2-af24d6b6ec5d

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem solution (ω : Ω) : 0 ≤ positivePart X ω := by
  exact le_max_right (X ω) 0
end PositiveNegativeParts
