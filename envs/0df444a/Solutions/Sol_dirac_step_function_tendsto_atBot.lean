-- Prove2me | solution 1 for dirac_step_function_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:43.725263+00:00
-- url     : https://prove2.me/submissions/21407d85-685b-416b-a675-d0c7bef553e6

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic
import Theorems.Thm_dirac_step_function_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Function Filter

theorem solution (x₀ : ℝ) :
    Tendsto (dirac_step_function x₀) atBot (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atBot.2 ?_
  refine ⟨x₀ - 1, ?_⟩
  intro x hx
  have hxx₀ : x < x₀ := by linarith
  simp [dirac_step_function_apply, hxx₀]
