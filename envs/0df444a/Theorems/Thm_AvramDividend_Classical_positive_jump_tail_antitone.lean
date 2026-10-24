-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_antitone
-- name    : AvramDividend.Classical.positive_jump_tail_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:04:24.897926+00:00
-- url     : https://prove2.me/theorems/db9a64a8-094e-48a7-bb94-29ca4baa56e5
-- title:
--   Positive jump-magnitude strict tail is antitone without σ-finiteness
-- statement:
--   For every measure on nonnegative jump magnitudes, the strict tail μ{z:t<z} decreases with t. This is the exact tail kernel used in BV Esscher renewal-series estimates and requires no local finiteness or SFinite assumption.
-- source:
--   Order monotonicity of nested measurable upper-tail sets under a positive measure.

import Mathlib.MeasureTheory.Integral.Layercake
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem positive_jump_tail_antitone (μ : Measure ℝ≥0) :
    Antitone (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) := by sorry
end AvramDividend.Classical
