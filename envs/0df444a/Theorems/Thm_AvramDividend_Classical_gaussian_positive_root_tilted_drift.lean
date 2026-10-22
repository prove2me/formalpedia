-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_tilted_drift
-- name    : AvramDividend.Classical.gaussian_positive_root_tilted_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:08.10847+00:00
-- url     : https://prove2.me/theorems/0f467759-6c37-47f8-9381-32b25762dbc1
-- title:
--   Positive Gaussian Esscher q-root forces positive corrected drift
-- statement:
--   For a nonnegative Gaussian quadratic coefficient, Lévy truncated-square integrability, positive Esscher root φ and positive discount q satisfying ψ(φ)=q, the Esscher-corrected drift b+2aφ+∫(k(z)-z exp(-φz))μ(dz) is strictly positive. The proof combines the integrated jump secant inequality with aφ²≥0 to obtain q≤φ dφ. This removes the extra drift-sign assumption used in the previously Proved strict Gaussian q-resolvent denominator theorem, within the canonical positive jump-magnitude formulation.
-- source:
--   Integrated pointwise exponential secant bound, Gaussian variance nonnegative and Esscher root equation.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_positive_root_tilted_drift (μ : Measure ℝ) (b a q φ : ℝ)
    (ha : 0 ≤ a) (hq : 0 < q) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    0 < b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ) := by sorry
