-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_damped_signed_kernel_untwist
-- name    : AvramDividend.Classical.causal_exp_damped_signed_kernel_untwist
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:41:35.043318+00:00
-- url     : https://prove2.me/theorems/d2faa837-d0d5-49ef-95b1-a00b067a500b
-- title:
--   Untwist the Gaussian damped signed kernel on positive time
-- statement:
--   For positive time t, multiplying the Gaussian signed damped kernel by exp(w t) recovers the undamped Volterra kernel -a⁻¹(β+K(t)). This identifies the kernel in the weighted primitive recurrence with the exact derivative-resolvent kernel needed for Gaussian C2 smoothness.
-- source:
--   Use the positive-time branch of the kernel definition, the exponential addition law exp(z)exp(-z)=1 and commutative-ring normalization. This is the pointwise reduction from the damped Neumann recursion to the original Esscher kernel β+K.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.causal_exp_damped_signed_kernel_untwist
    (a w β : ℝ) (K : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    Real.exp (w * t) *
      (if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) =
        -a⁻¹ * (β + K t) := by sorry
