-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_root_volterra_denominator
-- name    : AvramDividend.Classical.gaussian_esscher_root_volterra_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:10:14.307843+00:00
-- url     : https://prove2.me/theorems/77bcca45-31d4-407c-9160-610b262d61fe
-- title:
--   Gaussian Esscher root q-resolvent Volterra denominator identity
-- statement:
--   Under a Lévy truncated-square jump integrability condition, with a positive Esscher cutoff φ satisfying the canonical real Lévy–Khintchine root condition ψ(φ)=q and positive Laplace θ, the q-resolvent denominator ψ(φ+θ)-q equals the corrected Esscher drift times θ plus Gaussian quadratic term plus θ² times the finite real Gaussian double-tail Laplace transform. This is the exact algebraic denominator needed for a q-scale-function Volterra resolvent, independent of stochastic regularity claims.
-- source:
--   Proved gaussian_levy_esscher_volterra_real and the defining positive Esscher root relation ψ(φ)=q.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_root_volterra_denominator (μ : Measure ℝ) [SFinite μ] (b a q φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot :
      b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q =
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
