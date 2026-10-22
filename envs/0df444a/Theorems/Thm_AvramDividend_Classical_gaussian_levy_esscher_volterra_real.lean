-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_volterra_real
-- name    : AvramDividend.Classical.gaussian_levy_esscher_volterra_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:52:25.317558+00:00
-- url     : https://prove2.me/theorems/22be1408-b8f3-4f69-b6e4-c7d7d4b987e9
-- title:
--   Exact Gaussian Levy-Khintchine Esscher Volterra transform
-- statement:
--   For an Esscher cutoff φ>0 and Laplace variable θ>0 under the Lévy truncated-square condition and SFinite jump measure, the canonical real spectrally negative Lévy exponent difference equals corrected linear Esscher drift, Gaussian quadratic θ², and θ² times the real-valued positive double-tail Laplace integral. The representation follows from the Proved real Esscher exponent shift and the dependent real Tonelli-to-Bochner Laplace bridge. It is a critical analytic input to Gaussian scale-function Volterra regularity.
-- source:
--   Proved gaussian_levy_esscher_shift_real and pending gaussian_double_tail_laplace_real_bridge.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_levy_esscher_volterra_real (μ : Measure ℝ) [SFinite μ] (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
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
        θ ^ 2 *
          (∫⁻ t : ℝ, ∫⁻ z : ℝ,
            (if 0 < t ∧ t < z then
              ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
                ENNReal.ofReal (Real.exp (-φ * z))
             else 0) ∂μ ∂volume).toReal := by sorry
