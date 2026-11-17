-- Prove2me | solution 1 for negativePart_eq_max_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:32:39.076777+00:00
-- url     : https://prove2.me/submissions/986bf2fc-16d6-4380-ab4f-a35643bceb34

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem solution (X : Ω → ℝ) :
    negativePart X = fun ω => max (-X ω) 0 := by
  funext ω
  simpa [negativePart] using (max_neg_neg (X ω) (0 : ℝ)).symm
end PositiveNegativeParts
