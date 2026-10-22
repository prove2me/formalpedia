-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_integral_pushforward
-- name    : AvramDividend.Classical.gaussian_negative_jump_integral_pushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:23.061885+00:00
-- url     : https://prove2.me/theorems/e54d4f8a-57f0-4110-b3b7-ca6f54f28e0e
-- title:
--   Exact signed-to-positive Lévy jump integral pushforward
-- statement:
--   For any measure on the real line and a measurable real integrand F, integrating F(-y) over negative jumps against the original measure equals integrating F(z) over positive jump magnitudes against the pushforward under negation. This follows from the exact half-line preimage equality, pinned Measure.restrict_map and the general Bochner integral_map identity. It is a reusable noncircular change-of-variables bridge from the mission's negative-jump Lévy measure to the positive-magnitude measure required by the already proved Gaussian Esscher Volterra integral identities. The half-line and boundary conventions are preserved.
-- source:
--   Pinned exact-revision Mathlib MeasureTheory.Measure.restrict_map and MeasureTheory.integral_map.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_negative_jump_integral_pushforward (ν : Measure ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ y in Iio (0 : ℝ), F (-y) ∂ν) =
      ∫ z in Ioi (0 : ℝ),
        F z ∂(ν.map (fun y : ℝ => -y)) := by sorry
