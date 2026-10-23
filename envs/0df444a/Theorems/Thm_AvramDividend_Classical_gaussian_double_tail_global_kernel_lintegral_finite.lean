-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_kernel_lintegral_finite
-- name    : AvramDividend.Classical.gaussian_double_tail_global_kernel_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:05:38.181885+00:00
-- url     : https://prove2.me/theorems/983133a3-ca48-49f5-ad3e-4364f0b6d1c1
-- title:
--   Finite total mass of the Gaussian Esscher double-tail time kernel
-- statement:
--   The time-integrated Gaussian Esscher double-tail kernel has finite global mass under the Lévy truncated-square condition. The exact global Tonelli identity converts the mass to ∫exp(-φz)z²/2 μ(dz), bounded by the already proved exponentially damped quadratic jump moment. This is the L1-kernel hypothesis needed for Volterra C1 smoothing.
-- source:
--   gaussian_double_tail_global_area_tonelli and Proved gaussian_esscher_damped_quadratic_integrable

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_global_kernel_lintegral_finite (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ) (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) : (∫⁻ t : ℝ, ∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) < ⊤ := by sorry
