-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
-- name    : AvramDividend.Classical.avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:20:45.95284+00:00
-- url     : https://prove2.me/theorems/fce7ec07-8900-423a-b245-22a6686c5285
-- title:
--   Exact finite negative-mark compensated rate on every original uniform physical-grid cell
-- statement:
--   The original nnreal physical mesh has cell boundaries j*n/(m+1) and every adjacent difference equals n/(m+1), so the toReal value of the actual finite negative Lévy measure intensity of each cell equals its exact real width times the toReal mark intensity. This validates use of original marked-grid isometry alongside the uniform total intensity budget.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
    (n m i : ℕ) (mass : ℝ≥0∞) :
    (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
     let grid : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * Δ
     ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * mass).toReal)) =
      ((n : ℝ) / ((m : ℝ) + 1)) * mass.toReal := by sorry
