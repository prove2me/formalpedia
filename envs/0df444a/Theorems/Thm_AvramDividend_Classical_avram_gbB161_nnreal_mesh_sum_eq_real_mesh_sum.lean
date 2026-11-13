-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
-- name    : AvramDividend.Classical.avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:45:16.249581+00:00
-- url     : https://prove2.me/theorems/673038c8-281e-4dd9-b46b-1814e25ad1e7
-- title:
--   Original NNReal grid step sum equals corresponding real mesh step sum
-- statement:
--   For every uniform mesh size, the full NNReal grid cell indicator sum is exactly the corresponding real-valued uniform grid cell indicator sum, with the same original coefficient at each index. A pure algebraic bridge for B154 and B102/B139.
-- source:
--   NNReal coercion arithmetic

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_uniform_real_mesh_sum_bound_on_cells
open Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
    (n m : ℕ) (t : ℝ) (c : ℕ → ℝ) :
    let Δnn : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let Δr : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    (Finset.range (m + 1)).sum (fun i =>
      if (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ)
      then c i else 0) =
    (Finset.range (m + 1)).sum (fun i =>
      if (i : ℝ) * Δr ≤ t ∧
          t < (((i + 1 : ℕ) : ℝ) * Δr)
      then c i else 0) := by sorry
