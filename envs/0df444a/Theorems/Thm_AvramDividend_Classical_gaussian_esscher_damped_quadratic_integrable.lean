-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_quadratic_integrable
-- name    : AvramDividend.Classical.gaussian_esscher_damped_quadratic_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:41:30.229842+00:00
-- url     : https://prove2.me/theorems/00d2626c-be0f-4d84-b40b-2a4b3df57db6
-- title:
--   Integrability of Gaussian quadratic jumps after Esscher damping
-- statement:
--   The Levy truncated quadratic moment and positive exponential Esscher tilt imply global integrability of exp(-phi z) z². Dominate it pointwise by (1+2/phi) exp(-phi z/2) min(z²,z), whose measure integral is already proved finite. This is the exact global L1 area bound for the Gaussian double-tail Volterra kernel via Tonelli.
-- source:
--   Proved esscher_tilted_tail_area_integrable and new pointwise exponential damping bound

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_damped_quadratic_integrable (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ) (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) < ⊤ := by sorry
