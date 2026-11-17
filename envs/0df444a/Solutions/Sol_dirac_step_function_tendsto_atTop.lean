-- Prove2me | solution 1 for dirac_step_function_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:30:37.803462+00:00
-- url     : https://prove2.me/submissions/5ac7c89c-2ae2-40ba-b481-c7ed1e6e919e

import Theorems.Thm_dirac_step_function_tendsto_atBot
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
    Tendsto (dirac_step_function x₀) atTop (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atTop.2 ?_
  refine ⟨x₀, ?_⟩
  intro x hx
  have hxx₀ : ¬ x < x₀ := not_lt.mpr hx
  simp [dirac_step_function_apply, hxx₀]
