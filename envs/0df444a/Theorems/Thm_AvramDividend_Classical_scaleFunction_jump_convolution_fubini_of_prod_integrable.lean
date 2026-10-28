-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_fubini_of_prod_integrable
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-26T09:34:23.439546+00:00
-- url     : https://prove2.me/theorems/56268687-e99a-4ee0-b64b-d5d5b9cdaec6
-- title:
--   Weighted scale-jump Fubini interchange under product integrability
-- statement:
--   For the weighted q-scale jump convolution, product integrability on the positive-reserve by negative-jump measure allows direct interchange of the Bochner integrals. First move the reserve-dependent exponential scalar inside the jump integral; then apply the Mathlib product-integral Fubini theorem to the restricted measures. This is the exact abstract step needed after proving product integrability from finite jump activity.
-- source:
--   Mathlib.MeasureTheory.Integral.Prod.integral_integral_swap and Mathlib.MeasureTheory.Integral.Bochner.Basic.integral_const_mul.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Prod
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hint : Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) := by sorry
