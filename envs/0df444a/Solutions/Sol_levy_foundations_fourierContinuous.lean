-- Prove2me | solution 1 for levy_foundations_fourierContinuous
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:22:49.068642+00:00
-- url     : https://prove2.me/submissions/b12be8cc-5886-455f-9fa0-40fa03539b13

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Definitions.Def_levy_foundations_measureFourier

open MeasureTheory

theorem solution (μ : FiniteMeasure ℝ) :
    Continuous (LevyFoundations.measureFourier μ) := by
  unfold LevyFoundations.measureFourier
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · intro ξ
    exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑(ξ * x) * Complex.I)).aestronglyMeasurable
  · intro ξ
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Complex.norm_exp_ofReal_mul_I]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun x => ?_
    fun_prop
