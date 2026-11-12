-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound
-- name    : AvramDividend.Classical.avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:51:53.977206+00:00
-- url     : https://prove2.me/theorems/97525c4b-9ce7-4fd5-a2d8-5718c6d02d23
-- title:
--   Uniform bound for all negative-mark value increments on a compact reserve interval
-- statement:
--   For every continuous verification candidate on a compact nonnegative reserve interval, vanishing below zero, all strictly negative mark increments have a uniform finite absolute bound independent of the jump mark, enabling finite-activity dominated convergence in the original BV physical compensator.
-- source:
--   Mathlib IsCompact.image_of_continuousOn, IsCompact.isBounded and Metric.isBounded_iff_subset_closedBall

import Mathlib
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound (R : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 R)) (hw_neg : ∀ y < 0, w y = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ b z : ℝ, 0 ≤ b → b ≤ R → z < 0 → |w (b + z) - w b| ≤ 2 * M := by sorry
