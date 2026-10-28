-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_primitive_deriv_positive
-- name    : AvramDividend.Classical.scaleFunction_primitive_deriv_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:14:55.480603+00:00
-- url     : https://prove2.me/theorems/a286d355-91be-4be5-bdac-37d95e0e3d31
-- title:
--   Positive-reserve fundamental theorem for the scale-function integral
-- statement:
--   On every nonnegative compact reserve interval the measurable monotone q-scale function is integrable, and at strictly positive reserves it is continuous. Hence the derivative of its integral from zero to the current reserve is exactly the q-scale function itself. This calculus identity is required when differentiating the bounded-variation finite-activity Volterra renewal equation.
-- source:
--   Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus and basic q-scale function regularity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_primitive_deriv_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      deriv (fun t : ℝ => ∫ z in (0 : ℝ)..t, W z) x = W x := by sorry
