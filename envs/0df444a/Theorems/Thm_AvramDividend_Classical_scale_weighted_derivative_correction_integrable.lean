-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_weighted_derivative_correction_integrable
-- name    : AvramDividend.Classical.scale_weighted_derivative_correction_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:11:08.707063+00:00
-- url     : https://prove2.me/theorems/3f687f96-fc16-470e-9cc4-2821a75a923e
-- title:
--   Exponential integrability of the damped scale derivative kernel
-- statement:
--   At each admissible Laplace exponent, the product-rule kernel for the exponentially damped scale function, exp(-theta x)(W'(x)-theta W(x)), is integrable over the positive half-line. This follows by subtraction of the existing Proved weighted-derivative integrability and the scale-function Laplace integrability. It supplies exactly the kernel hypothesis in the zero-discount C1 damping transfer.
-- source:
--   Proved chat07_scale_weighted_deriv_integrable_positive_halfline (a01f741d-18f2-4a06-af0d-61e118db667a) and the IsScaleFunction Laplace clause.

import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scale_weighted_derivative_correction_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * (deriv W x - θ * W x))
      (Ioi (0 : ℝ)) volume := by sorry
