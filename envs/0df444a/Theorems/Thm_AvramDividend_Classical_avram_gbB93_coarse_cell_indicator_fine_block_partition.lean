-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB93_coarse_cell_indicator_fine_block_partition
-- name    : AvramDividend.Classical.avram_gbB93_coarse_cell_indicator_fine_block_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:43:31.039197+00:00
-- url     : https://prove2.me/theorems/10d5d369-04da-43bb-a664-0b36634d23a7
-- title:
--   Every coarse half-open uniform cell is the disjoint union of its fine subcells
-- statement:
--   The indicator of any coarse half-open uniform cell of width n/(m+1) equals the sum of indicators of its b consecutive fine half-open subcells of width n/((m+1)b). This identity holds pointwise in real time, including endpoints.
-- source:
--   Deterministic partition-geometry child of B91 coarse-step refinement.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB93_coarse_cell_indicator_fine_block_partition
    (n m b i : ℕ) (hn : 0 < n) (hb : 0 < b) (t : ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    (if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
      t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
     then (1 : ℝ) else 0) =
    (Finset.range b).sum (fun j =>
      if ((i * b + j : ℕ) : ℝ) * δ ≤ t ∧
        t < ((i * b + j + 1 : ℕ) : ℝ) * δ
      then (1 : ℝ) else 0) := by sorry
