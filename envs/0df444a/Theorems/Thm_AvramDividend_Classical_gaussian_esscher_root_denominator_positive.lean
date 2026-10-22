-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_root_denominator_positive
-- name    : AvramDividend.Classical.gaussian_esscher_root_denominator_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:13:11.502476+00:00
-- url     : https://prove2.me/theorems/958a8558-e61d-4273-b320-c0b315aaf444
-- title:
--   Strict positivity of Gaussian Esscher q-resolvent denominator
-- statement:
--   For a spectrally negative real Lévy-Khintchine exponent with strictly positive Gaussian quadratic coefficient, a positive Esscher root ψ(φ)=q, positive θ and nonnegative corrected Esscher drift, the q-resolvent denominator ψ(φ+θ)-q is strictly positive. The proof uses the separately Proved sharp Gaussian quadratic lower bound and the positive Gaussian θ² term. This supplies the nonvanishing denominator needed for a rigorously justified q-scale Laplace resolvent without assuming the ultimate C1/C2 regularity.
-- source:
--   Proved gaussian_levy_esscher_shift_quadratic_lower_real, Gaussian variance a>0, tilted drift dφ≥0 and root condition ψ(φ)=q.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_esscher_root_denominator_positive (μ : Measure ℝ) (b a q φ θ : ℝ)
    (ha : 0 < a) (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q)
    (hdrift : 0 ≤ b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) :
    0 < (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q := by sorry
