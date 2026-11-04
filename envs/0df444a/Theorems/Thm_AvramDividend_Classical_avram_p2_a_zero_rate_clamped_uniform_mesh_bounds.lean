-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:56:03.059158+00:00
-- url     : https://prove2.me/theorems/1c84ecc5-a08c-478b-ac73-2f259b027deb
-- title:
--   Clamped original uniform mesh cells satisfy global horizon and width bounds
-- statement:
--   Extend a finite uniform source grid to all natural-number cell indices by making indices above the final cell degenerate at the terminal horizon. Under exact horizon coverage, every extended left endpoint stays below T, every cell is ordered, and each width is bounded by δ. This allows the global triangular-grid hypotheses of the genuine reverse jump-matching theorem to be instantiated for the original finite uniform grid.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
    (T δ : ℝ≥0) (n i : ℕ)
    (hcover : ((n : ℝ≥0) + 1) * δ = T) :
    (if i ≤ n then (i : ℝ≥0) * δ else T) ≤ T ∧
    (if i ≤ n then (i : ℝ≥0) * δ else T) ≤
      (if i ≤ n then (((i + 1 : ℕ) : ℝ≥0) * δ) else T) ∧
    (if i ≤ n then (((i + 1 : ℕ) : ℝ≥0) * δ) else T) ≤
      (if i ≤ n then (i : ℝ≥0) * δ else T) + δ  := by sorry
