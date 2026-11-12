-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb88_single_block_original_time_ledger
-- name    : AvramDividend.Classical.avram_gb88_single_block_original_time_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:36:25.929794+00:00
-- url     : https://prove2.me/theorems/3ceae665-941a-4c67-9dbb-ea3516234dde
-- title:
--   Original-time centred coarse increment equals refined telescoping block
-- statement:
--   For any real path on NNReal time, drift and positive uniform refinement factor b, one original coarse-grid centred increment equals the difference of the drift-corrected path at the corresponding consecutive block boundaries on the fine grid. This converts NNReal original time and its drift into the integer finite-difference form used in gb83.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb88_single_block_original_time_ledger
    (n m b i : ℕ) (hb : 0 < b) (x : ℝ≥0 → ℝ) (c : ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
    let f : ℕ → ℝ := fun r => x ((r : ℝ≥0) * d) - (r : ℝ) * (d : ℝ) * c
    x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c =
      f ((i + 1) * b) - f (i * b) := by sorry
