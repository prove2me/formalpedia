-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_small_jump_weight_lower
-- name    : AvramDividend.Classical.esscher_small_jump_weight_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:38:52.624662+00:00
-- url     : https://prove2.me/theorems/5233b958-e351-4db3-8742-9f1cc9a496ff
-- title:
--   Small-jump exponential Esscher lower bound
-- statement:
--   For a nonnegative Esscher exponent and any jump size at least minus one, the exponential Esscher weighting is bounded below by exp(-phi). This will preserve divergence of the original small-jump first moment.
-- source:
--   Pinned Mathlib real exponential monotonicity and ENNReal.ofReal monotonicity

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_small_jump_weight_lower (φ y : ℝ) (hφ : 0 ≤ φ) (hy : -1 ≤ y) : ENNReal.ofReal (Real.exp (-φ)) ≤ ENNReal.ofReal (Real.exp (φ * y)) := by sorry
