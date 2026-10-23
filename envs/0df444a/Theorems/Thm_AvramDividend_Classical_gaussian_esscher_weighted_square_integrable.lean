-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_weighted_square_integrable
-- name    : AvramDividend.Classical.gaussian_esscher_weighted_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:43:13.432371+00:00
-- url     : https://prove2.me/theorems/1455760a-fcaf-4f65-a098-9b2a4d1b4dc5
-- title:
--   Integrability of exponentially damped squared Lévy jumps
-- statement:
--   Under the quadratic Levy condition, the exponentially damped squared positive jump size is integrable. Apply the pointwise Gaussian Esscher damping bound at positive tilt φ and the Proved tail-area integrability theorem at half tilt φ/2, then use ENNReal comparison of integrals.
-- source:
--   Pointwise Gaussian damping lemma a8063c69-f417-4a85-8c5e-62d33500c463 and Proved tail-area lemma 86325105-592c-46ca-a50d-8f37a12fb484.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_weighted_square_integrable
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) < ⊤ := by sorry
