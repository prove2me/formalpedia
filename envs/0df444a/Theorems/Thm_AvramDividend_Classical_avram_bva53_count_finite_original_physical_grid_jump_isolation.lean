-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva53_count_finite_original_physical_grid_jump_isolation
-- name    : AvramDividend.Classical.avram_bva53_count_finite_original_physical_grid_jump_isolation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:34:10.639203+00:00
-- url     : https://prove2.me/theorems/35e417f3-77c1-4185-8f56-9347e88f0e28
-- title:
--   Finite original jump counting mass gives eventual one jump per actual physical grid cell
-- statement:
--   Any original nonnegative jump-time set with finite counting mass has, eventually, at most one element in each half-open physical uniform-grid cell defined by the source u. The result is uniform over all grid indices and works without moving the original stochastic process to an auxiliary probability space.
-- source:
--   Combines direct Proved helpers avram_bva50_original_physical_u_grid_finite_jump_cell_isolation and avram_bva51_finite_count_mark_times_real_finset for physical finite-positive-jump source 4287fafd-afdc-46b2-a160-033b7b2500f2, 11 November 2026.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bva53_count_finite_original_physical_grid_jump_isolation (S : Set ℝ≥0) (hCount : (Measure.count S) < ⊤) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) : ∀ᶠ n : ℕ in Filter.atTop, ∀ i : ℕ, ∀ s t : ℝ≥0, s ∈ S → t ∈ S → u n i ≤ s → s < u n (i + 1) → u n i ≤ t → t < u n (i + 1) → s = t := by sorry
