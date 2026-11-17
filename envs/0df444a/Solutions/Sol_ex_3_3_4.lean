-- Prove2me | solution 1 for ex_3_3_4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:11:25.549205+00:00
-- url     : https://prove2.me/submissions/00e92893-1693-45b8-8b22-a7fa37865b3a

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

theorem solution (x₀ : ℝ) (A : Set ℝ) :
    (dirac_step_function x₀).measure A = A.indicator 1 x₀ := by
  rw [dirac_step_measure_eq_dirac]
  simp
