-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_derivative_primitive_at_zero
-- name    : AvramDividend.Classical.integrable_derivative_primitive_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:03:09.342601+00:00
-- url     : https://prove2.me/theorems/5df6c575-ef07-409c-a33b-f765c7b9f6db
-- title:
--   An integrable positive-time derivative recovers the zero-origin primitive
-- statement:
--   A continuous function vanishing at zero is recovered by integrating its derivative on the positive half-line, assuming that derivative is globally integrable there. Differentiability at zero is deliberately unnecessary, allowing a singular kernel at the boundary. This is the missing primitive step for exponentially damped zero-discount scale functions.
-- source:
--   Mathlib intervalIntegral.integral_deriv_eq_sub_uIoo, intervalIntegrable_iff_integrableOn_Ioc_of_le, and intervalIntegral.integral_congr_uIoo. Application uses weighted derivative integrability and g_theta(0)=0.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.integrable_derivative_primitive_at_zero
    (g k : ℝ → ℝ) (h0 : g 0 = 0)
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hk : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt g (k t) t) :
    ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x := by sorry
