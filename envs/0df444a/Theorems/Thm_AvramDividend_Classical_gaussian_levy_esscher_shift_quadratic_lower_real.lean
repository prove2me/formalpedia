-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_quadratic_lower_real
-- name    : AvramDividend.Classical.gaussian_levy_esscher_shift_quadratic_lower_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:59:47.275343+00:00
-- url     : https://prove2.me/theorems/f7a96971-4653-41ff-9e52-e0547f9ff407
-- title:
--   Gaussian quadratic lower bound for real Esscher-shifted Levy exponent
-- statement:
--   For φ>0 and θ≥0, any real drift and Gaussian coefficient and every positive jump-magnitude Lévy measure with truncated-square integrability, the full canonical real Lévy-Khintchine exponent increment is at least the corrected Esscher drift times θ plus the Gaussian quadratic coefficient times θ². This is an exact consequence of the fully Proved exponent shift and nonnegative compensated jump integral, using the real Bochner integral positivity theorem. It supplies a process-independent Gaussian lower bound for subsequent scale-function regularity analysis.
-- source:
--   Proved gaussian_levy_esscher_shift_real and gaussian_compensated_jump_pos_linear; pinned integral_nonneg_of_ae and ae_restrict_mem.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_esscher_shift_quadratic_lower_real (μ : Measure ℝ) (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    θ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) +
      a * θ ^ 2 ≤
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) -
      (b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ)) := by sorry
