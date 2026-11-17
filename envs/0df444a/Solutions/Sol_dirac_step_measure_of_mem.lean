-- Prove2me | solution 1 for dirac_step_measure_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:14:00.913378+00:00
-- url     : https://prove2.me/submissions/69b9652a-9ea0-4ff7-870d-14bad473d5c6

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

theorem solution (x₀ : ℝ) (A : Set ℝ) (hx : x₀ ∈ A) :
    (dirac_step_function x₀).measure A = 1 := by
  rw [ex_3_3_4]
  simp [hx]
