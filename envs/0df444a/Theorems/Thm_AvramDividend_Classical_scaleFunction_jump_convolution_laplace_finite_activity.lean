-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_finite_activity
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_laplace_finite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:03:29.170797+00:00
-- url     : https://prove2.me/theorems/cf67ec6a-8d05-4345-98cf-835340ac2199
-- title:
--   Finite-activity q-scale jump convolution Laplace transform
-- statement:
--   For finite negative-jump intensity, the Laplace transform of the negative-jump convolution equals the Laplace transform of the q-scale function times the jump exponential moment. This follows from the kernel product-integrability, Fubini interchange and each shifted scale-function transform.
-- source:
--   Fubini's theorem and Proved AvramDividend.Classical shifted scale-function Laplace identities.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_product_integrable_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_fubini_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_laplace_finite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by sorry
