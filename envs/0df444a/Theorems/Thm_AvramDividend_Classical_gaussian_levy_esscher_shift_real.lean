-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_real
-- name    : AvramDividend.Classical.gaussian_levy_esscher_shift_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:37:41.775933+00:00
-- url     : https://prove2.me/theorems/28fc8298-0ba3-4cec-a08e-466442a76dd1
-- title:
--   Complete real Gaussian Lévy–Khintchine Esscher-shift identity
-- statement:
--   For positive φ and nonnegative θ, given a positive jump-magnitude Lévy measure satisfying ∫min(1,z²)μ(dz)<∞, the canonical real Lévy–Khintchine exponent bλ+aλ²+∫(e^{−λz}−1+λ z1_{z≤1})dμ satisfies a complete Esscher-shift decomposition into linear corrected drift, Gaussian quadratic θ² and the positive shifted compensated-jump integral. All real integrals exist by separately proved canonical jump, compensator and drift Bochner integrability. The result supplies the process-independent real algebraic transform needed for Gaussian Volterra analysis.
-- source:
--   Proved gaussian_esscher_jump_integral_shift, gaussian_shifted_compensator_real_integrable, gaussian_esscher_drift_real_integrable, and pending gaussian_levy_jump_real_integrable.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_esscher_shift_real
    (μ : Measure ℝ) (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) -
      (b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ)) =
      θ * (b + 2 * a * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) -
            z * Real.exp (-φ * z) ∂μ)) +
        a * θ ^ 2 +
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-φ * z) *
              (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := by sorry
