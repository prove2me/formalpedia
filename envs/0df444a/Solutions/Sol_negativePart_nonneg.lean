-- Prove2me | solution 1 for negativePart_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:00.262209+00:00
-- url     : https://prove2.me/submissions/611df323-2884-4fe4-bf06-8596ecc1fbd7

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem solution (ω : Ω) : 0 ≤ negativePart X ω := by
  simp [negativePart]
end PositiveNegativeParts
