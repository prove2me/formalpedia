-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_double_tail_global_mass_finite
-- name    : AvramDividend.Classical.gaussian_esscher_double_tail_global_mass_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:06:17.46498+00:00
-- url     : https://prove2.me/theorems/b3d3df3d-f813-4c20-b748-aadbed16493c
-- title:
--   Global finite mass of the Gaussian Esscher double-tail kernel
-- statement:
--   For a sigma-finite positive jump measure satisfying the Levy truncated-square condition and positive Esscher tilt, the time-first Gaussian double-tail kernel has finite total ENNReal mass. Tonelli reduces this to an exponentially damped quadratic jump moment, already proved integrable. The only remaining geometric input is the exact global double-tail area identity.
-- source:
--   Proved gaussian_esscher_damped_quadratic_integrable combined with gaussian_double_tail_global_area_tonelli and the pointwise half-square domination.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_double_tail_global_mass_finite
    (μ : Measure ℝ) [SFinite μ]
    (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z)))
       else 0) ∂μ ∂volume) < ⊤ := by sorry
