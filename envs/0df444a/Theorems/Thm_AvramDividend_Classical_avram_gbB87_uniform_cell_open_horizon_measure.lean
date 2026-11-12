-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB87_uniform_cell_open_horizon_measure
-- name    : AvramDividend.Classical.avram_gbB87_uniform_cell_open_horizon_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:03:57.375755+00:00
-- url     : https://prove2.me/theorems/b7de098d-ec71-4a88-96c2-de277c9862b0
-- title:
--   Uniform half-open cell meets the open horizon in exactly one cell-width measure
-- statement:
--   The Lebesgue measure of a uniform half-open cell intersected with the open positive horizon equals the uniform cell width. Its only possible lost point is the zero endpoint, which is null.
-- source:
--   Interval geometry child of the original scalar indicator integral B86.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB87_uniform_cell_open_horizon_measure
    (n N r : ℕ) (hn : 0 < n) (hN : 0 < N) (hr : r < N) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (volume (Ioo (0 : ℝ) (n : ℝ) ∩
      Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ))).toReal = δ := by sorry
