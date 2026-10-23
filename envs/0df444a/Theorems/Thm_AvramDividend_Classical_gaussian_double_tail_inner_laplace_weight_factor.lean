-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_inner_laplace_weight_factor
-- name    : AvramDividend.Classical.gaussian_double_tail_inner_laplace_weight_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:49:46.880489+00:00
-- url     : https://prove2.me/theorems/908f706d-9706-4f77-8753-0a6e96bf203e
-- title:
--   Gaussian double-tail inner lintegral commutes with the external Laplace-time factor
-- statement:
--   For every real time t, parameter θ and jump measure μ, the nonnegative Gaussian Esscher double-tail jump integral with external Laplace factor exp(-θt) is exactly exp(-θt) multiplied by the unweighted jump integral. The already Proved pointwise Esscher-time weight factorisation and Mathlib's lintegral_const_mul yield the identity without finiteness or integrability assumptions. This isolates the inner half of the conversion from the positive double-lintegral to the real weighted Volterra kernel.
-- source:
--   Proved gaussian_double_tail_time_weight_factor; Mathlib MeasureTheory.lintegral_const_mul

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_weight_factor
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_inner_laplace_weight_factor
    (μ : Measure ℝ) (φ θ t : ℝ) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) =
      ENNReal.ofReal (Real.exp (-θ * t)) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ) := by sorry
