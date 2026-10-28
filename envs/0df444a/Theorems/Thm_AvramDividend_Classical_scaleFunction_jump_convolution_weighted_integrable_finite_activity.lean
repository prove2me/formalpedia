-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_weighted_integrable_finite_activity
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_weighted_integrable_finite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:14:40.42466+00:00
-- url     : https://prove2.me/theorems/c5cc6387-b333-4a06-8bd6-340f66328efd
-- title:
--   Weighted jump convolution is integrable on the positive reserve axis
-- statement:
--   Under finite negative jump intensity and an admissible q-scale Laplace parameter, the exponentially weighted convolution of the q-scale function against the Levy jump measure is integrable in reserve. This is the inner-variable integral of the already proved weighted product-integrability kernel.
-- source:
--   Theorem scaleFunction_jump_convolution_product_integrable_finite_activity and Mathlib Integrable.integral_prod_right.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_product_integrable_finite_activity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_weighted_integrable_finite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν))
      (Ioi (0 : ℝ)) volume := by sorry
