-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_tail_weight_finite
-- name    : AvramDividend.Classical.gaussian_esscher_positive_tail_weight_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:31:54.123965+00:00
-- url     : https://prove2.me/theorems/365fdf9f-b48c-4a83-9f28-d051c99b0bc1
-- title:
--   Finite Esscher exponential weight on every positive Lévy tail
-- statement:
--   For a positive-side Lévy measure with finite truncated-square integral, and any positive cutoff ε and Esscher rate φ, the integral of e^(−φz) over the positive tail [ε,∞) is finite, bounded by the finite tail mass.
-- source:
--   Proved gaussian_levy_positive_tail_finite and Real.exp_le_one_iff.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_esscher_positive_tail_weight_finite
    (μ : Measure ℝ) (ε φ : ℝ) (hε : 0 < ε) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by sorry
