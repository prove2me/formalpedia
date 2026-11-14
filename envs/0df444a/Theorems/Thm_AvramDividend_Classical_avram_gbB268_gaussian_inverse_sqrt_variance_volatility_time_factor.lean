-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
-- name    : AvramDividend.Classical.avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:35:45.863213+00:00
-- url     : https://prove2.me/theorems/d5f5f29e-4a80-4924-b874-e796d97fb213
-- title:
--   Gaussian inverse square root density separates positive volatility from elapsed-time kernel
-- statement:
--   For positive original Gaussian volatility sigma and nonnegative elapsed time dt, the reciprocal square root of twice pi times sigma squared times dt factors exactly into the reciprocal of sqrt of twice pi, the reciprocal of sigma and the reciprocal of sqrt of dt. This formally separates the source volatility constant from the integrable elapsed-time singularity in fixed-level Gaussian controlled-reserve occupation arguments. The identity is valid at zero via Lean reciprocal convention.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
    (sigma dt : ℝ) (hsigma : 0 < sigma) (hdt : 0 ≤ dt) :
    (Real.sqrt (2 * Real.pi * (sigma ^ 2 * dt)))⁻¹ =
      (Real.sqrt (2 * Real.pi))⁻¹ * sigma⁻¹ * (Real.sqrt dt)⁻¹ := by sorry
