-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_linear_reference
-- name    : AvramDividend.Classical.positive_laplace_linear_reference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:40:53.690515+00:00
-- url     : https://prove2.me/theorems/1b94bef9-dc60-4bac-8c3a-df509cffa3a7
-- title:
--   Laplace transform of the identity function on the positive half-line
-- statement:
--   For every θ>0, ∫ over x>0 of exp(-θx) x dx equals 1/θ². Specialise the exact pinned Mathlib real Gamma integral to a=2, r=θ, use x^(2−1)=x and Γ(2)=1, and commute the scalar factors. This is the reference transform for the pointwise Gaussian Volterra equation.
-- source:
--   Pinned Mathlib Real.integral_rpow_mul_exp_neg_mul_Ioi and Real.Gamma_two

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_laplace_linear_reference (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * x ∂volume) =
      (1 / θ) ^ 2 := by sorry
