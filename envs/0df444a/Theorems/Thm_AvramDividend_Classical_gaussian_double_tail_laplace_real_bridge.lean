-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_laplace_real_bridge
-- name    : AvramDividend.Classical.gaussian_double_tail_laplace_real_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:48:24.138645+00:00
-- url     : https://prove2.me/theorems/87f923ad-e154-4bdf-8563-4d4ad0463c9c
-- title:
--   Exact real Gaussian Esscher double-tail Laplace identity
-- statement:
--   For a positive Esscher cutoff and positive Laplace time parameter, under the standard Lévy truncated-square moment the finite ENNReal Gaussian double-tail time-first transform, converted toReal, multiplied by θ², equals the actual real Bochner integral of the Esscher quadratic jump compensator. Combine the Proved ENNReal Tonelli/atom transform with independently Proved real compensator integrability and nonnegativity, then use exact ENNReal/Bochner integral coercion identities. This is an essential real-to-extended-nonnegative bridge towards a Gaussian Volterra renewal equation.
-- source:
--   Proved gaussian_double_tail_esscher_laplace_transform, gaussian_shifted_compensator_real_integrable, gaussian_compensated_jump_pos_linear; pinned ofReal_integral_eq_lintegral_ofReal, integral_nonneg_of_ae and ENNReal.toReal_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_laplace_real_bridge
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    θ ^ 2 *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume).toReal =
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := by sorry
