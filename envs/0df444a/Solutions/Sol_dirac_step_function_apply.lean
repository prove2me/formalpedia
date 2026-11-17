-- Prove2me | solution 1 for dirac_step_function_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:16:18.484059+00:00
-- url     : https://prove2.me/submissions/a0b3333d-adeb-4694-95f2-48c0522d62b0

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic


/-

  # Example 3.3.4 Dirac measure

-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Function Filter


theorem solution (x₀ x : ℝ) :
    dirac_step_function x₀ x = if x < x₀ then 0 else 1 := by
  rw [dirac_step_function, Monotone.stieltjesFunction_eq]
  by_cases hx : x < x₀
  · apply rightLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show x < (x + x₀) / 2 by linarith)] with y hy
    have hmid : (x + x₀) / 2 < x₀ := by linarith
    have hyx₀ : y < x₀ := lt_trans hy.2 hmid
    have hval : dirac_step_fun x₀ y = 0 := by
      simp [dirac_step_fun, hyx₀]
    simpa [hval]
  · apply rightLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show x < x + 1 by linarith)] with y hy
    have hx₀ : x₀ ≤ x := le_of_not_gt hx
    have hyx₀ : ¬ y < x₀ := by linarith [le_of_not_gt hx, hy.1]
    have hval : dirac_step_fun x₀ y = 1 := by
      simp [dirac_step_fun, hyx₀]
    simpa [hval]