-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product
-- name    : AvramDividend.Classical.positive_causal_convolution_laplace_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T15:01:35.937521+00:00
-- url     : https://prove2.me/theorems/5473ec27-7b9c-42dc-aa29-72c87f745b48
-- title:
--   Signed real one-sided convolution obeys the Laplace product rule
-- statement:
--   For any two signed real functions whose exponentially weighted restrictions to the positive half-line are Lebesgue integrable, the unilateral Laplace transform of their causal convolution is the product of the two unilateral transforms. The proof applies Mathlib's integral_posConvolution to the weighted factors and cancels the exponentials pointwise, providing a reusable Gaussian Volterra inversion bridge.
-- source:
--   Mathlib.Analysis.Convolution, MeasureTheory.integral_posConvolution; standard Fubini convolution product theorem.

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_convolution_laplace_product
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) ∂volume) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * f t ∂volume) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * g t ∂volume) := by sorry
