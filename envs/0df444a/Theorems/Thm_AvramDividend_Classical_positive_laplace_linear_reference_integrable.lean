-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_linear_reference_integrable
-- name    : AvramDividend.Classical.positive_laplace_linear_reference_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:43:30.861564+00:00
-- url     : https://prove2.me/theorems/96dacfca-2c96-4670-8f0a-ab5bff4b4330
-- title:
--   Weighted identity function is integrable over the positive half-line
-- statement:
--   For θ>0 the first positive moment of the exponential kernel is Lebesgue integrable: exp(-θx)x∈L¹((0,∞)). This is the a=1, s=1, b=θ instance of the Mathlib integrableOn_rpow_mul_exp_neg_mul_rpow theorem, followed by x^1=x and commutativity of real multiplication. Needed to apply the signed-Laplace uniqueness theorem to the pointwise Volterra equation.
-- source:
--   Pinned Mathlib integrableOn_rpow_mul_exp_neg_mul_rpow

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_laplace_linear_reference_integrable (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * x)
      (Ioi (0 : ℝ)) volume := by sorry
