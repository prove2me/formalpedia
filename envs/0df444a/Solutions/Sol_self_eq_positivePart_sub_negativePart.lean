-- Prove2me | solution 1 for self_eq_positivePart_sub_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:51:43.5038+00:00
-- url     : https://prove2.me/submissions/76a9b3b9-0e21-4161-85e2-f38e9626f7fe

import Theorems.Thm_negativePart_eq_max_neg
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
    X = fun ω => positivePart X ω - negativePart X ω := by
  funext ω
  rw [negativePart_eq_max_neg]
  simp only [positivePart,
    max_zero_sub_max_neg_zero_eq_self]
end PositiveNegativeParts
