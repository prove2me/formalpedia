-- Prove2me | solution 1 for dirac_step_measure_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:14:08.740994+00:00
-- url     : https://prove2.me/submissions/e61d7110-90c4-4228-8a3c-85d7a38f0b48

import Theorems.Thm_ex_3_3_4
import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Function Filter

theorem solution (x₀ : ℝ) (A : Set ℝ) (hx : x₀ ∉ A) :
    (dirac_step_function x₀).measure A = 0 := by
  rw [ex_3_3_4]
  simp [hx]
