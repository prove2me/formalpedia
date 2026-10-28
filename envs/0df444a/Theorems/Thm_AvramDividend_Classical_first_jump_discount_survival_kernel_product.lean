-- Prove2me | Theorems.Thm_AvramDividend_Classical_first_jump_discount_survival_kernel_product
-- name    : AvramDividend.Classical.first_jump_discount_survival_kernel_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:07:19.199842+00:00
-- url     : https://prove2.me/theorems/5b3b5fe7-3f49-417e-8f85-f31ec3a57d31
-- title:
--   First-jump survival times discounted drift kernel is the combined-rate exponential
-- statement:
--   For any real drift d, discount q, jump rate lambda and time t, the extended-nonnegative first-jump exponential survival factor ENNReal.ofReal(exp(-lambda*t)) multiplied by the embedded discounted drift ENNReal.ofReal(d exp(-q*t)) equals ENNReal.ofReal(d exp(-(q+lambda)t)). The result is mathematically valid even for negative d because ENNReal.ofReal clips negative values and the survival factor is strictly positive. The proof uses the pinned ENNReal.ofReal_mul with positivity of the exponential, Real.exp_add, and ring normalisation. This removes the last algebraic kernel mismatch in combining the accepted strict-survival Tonelli result with the accepted deterministic drift integral.
-- source:
--   Avram Palmowski Pistorius 2007, §3.3 finite-activity first-jump reward; Mathlib exponential addition and ENNReal multiplication.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

open scoped ENNReal

theorem AvramDividend.Classical.first_jump_discount_survival_kernel_product
    (d q rate t : ℝ) :
    ENNReal.ofReal (Real.exp (-(rate * t))) *
      ENNReal.ofReal (d * Real.exp (-(q * t))) =
    ENNReal.ofReal (d * Real.exp (-((q + rate) * t))) := by sorry
