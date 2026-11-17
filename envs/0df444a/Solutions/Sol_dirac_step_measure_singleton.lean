-- Prove2me | solution 1 for dirac_step_measure_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:11:15.980853+00:00
-- url     : https://prove2.me/submissions/4b6ff666-1c57-4c1b-bc93-56532c6836b6

import Theorems.Thm_dirac_step_measure_eq_dirac
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

theorem solution (x₀ : ℝ) :
    (dirac_step_function x₀).measure {x₀} = 1 := by
  rw [dirac_step_measure_eq_dirac]
  simp
