-- Prove2me | solution 1 for dirac_step_measure_eq_dirac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:09:19.497873+00:00
-- url     : https://prove2.me/submissions/cced582a-a3e9-4b05-af58-45036a247d87

import Theorems.Thm_dirac_step_function_tendsto_atBot
import Theorems.Thm_dirac_step_function_tendsto_atTop
import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic
import Theorems.Thm_dirac_step_function_apply


/-

  # Example 3.3.4 Dirac measure

-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Function Filter


theorem solution (x₀ : ℝ) :
    (dirac_step_function x₀).measure = Measure.dirac x₀ := by
  have h_univ : (dirac_step_function x₀).measure univ = 1 := by
    simpa using
      (StieltjesFunction.measure_univ (dirac_step_function x₀)
        (dirac_step_function_tendsto_atBot x₀)
        (dirac_step_function_tendsto_atTop x₀))
  letI : IsFiniteMeasure ((dirac_step_function x₀).measure) := ⟨by simp [h_univ]⟩
  refine Measure.ext_of_Iic (dirac_step_function x₀).measure (Measure.dirac x₀) fun x => ?_
  rw [StieltjesFunction.measure_Iic (dirac_step_function x₀)
    (dirac_step_function_tendsto_atBot x₀)]
  by_cases hx : x < x₀
  · simp [dirac_step_function_apply, hx, not_le_of_gt hx]
  · simp [dirac_step_function_apply, hx, le_of_not_gt hx]