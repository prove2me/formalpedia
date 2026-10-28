-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_fubini_of_prod_integrable_levy_measure
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable_levy_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:38:27.971722+00:00
-- url     : https://prove2.me/theorems/a1269afc-8389-42fb-a9e8-40e529f40ab5
-- title:
--   Weighted Lévy-jump convolution Fubini from product integrability
-- statement:
--   For the weighted scale-function negative-jump convolution, integrability with respect to the product of positive-reserve Lebesgue measure and restricted negative-jump Lévy measure implies the exact exchange of integral order. All jump-coordinate integrals retain X.ν. This isolates product integrability as the remaining Fubini input for the finite-activity Volterra identity.
-- source:
--   Mathlib.MeasureTheory.Integral.Prod.integral_integral_swap and Mathlib.MeasureTheory.Integral.Bochner.Basic.integral_const_mul.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Prod
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable_levy_measure
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
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν := by sorry
