-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_resolvent_denominator
-- name    : AvramDividend.Classical.gaussian_positive_root_resolvent_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:13.317462+00:00
-- url     : https://prove2.me/theorems/222cdad9-8997-421a-950c-40195ea64e08
-- title:
--   Positive Gaussian q-resolvent without an assumed tilted drift sign
-- statement:
--   A Lévy-Khintchine exponent with strictly positive Gaussian quadratic coefficient and jump truncated-square integrability has strictly positive increment ψ(φ+θ)-q whenever φ>0 satisfies ψ(φ)=q>0 and θ>0. The corrected tilted drift is positive by the independently proved integrated secant inequality, so the previously proved Gaussian quadratic lower bound applies without an extra drift-sign assumption. This theorem supplies a genuine positive-root resolvent denominator for the Gaussian Volterra programme.
-- source:
--   Proved gaussian_esscher_root_denominator_positive and the newly published gaussian_positive_root_tilted_drift dependency.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_positive_root_resolvent_denominator (μ : Measure ℝ) (b a q φ θ : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    0 < (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q := by sorry
