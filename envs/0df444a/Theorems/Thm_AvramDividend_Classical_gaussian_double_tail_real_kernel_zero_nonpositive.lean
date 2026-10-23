-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_zero_nonpositive
-- name    : AvramDividend.Classical.gaussian_double_tail_real_kernel_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:29:51.725742+00:00
-- url     : https://prove2.me/theorems/dc4d7d53-2a3b-489c-b4c6-75bc54003977
-- title:
--   Gaussian Esscher double-tail kernel vanishes at nonpositive times
-- statement:
--   The Gaussian Esscher double-tail kernel has causal support: for every nonpositive time t the condition 0<t is false, so the ENNReal jump integral is exactly zero and its real conversion is zero. This is the support input when interpreting the Laplace transform as a causal convolution.
-- source:
--   Source-neutral indicator simplification

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_kernel_zero_nonpositive (μ : Measure ℝ) (φ t : ℝ) (ht : t ≤ 0) : (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal = 0 := by sorry
