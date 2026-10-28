-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_uniform_time_grid_with_reciprocal_width
-- name    : AvramDividend.Classical.nonnegative_uniform_time_grid_with_reciprocal_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:15:52.080156+00:00
-- url     : https://prove2.me/theorems/730fa062-f661-4023-bc1b-ba1e4238aff5
-- title:
--   Exact equal-duration NNReal mesh exists with cell width equal to total horizon divided by cell count
-- statement:
--   The already proved existence of a nonnegative-real uniform grid gives ordered cells in a finite horizon, constant cell length delta, and N*delta=T. When N is positive it is invertible as a nonnegative real, so the cell width is exactly delta=T/N. This strengthens the earlier grid existence theorem with the reciprocal formula needed to choose a time mesh whose cell count increases, and to identify the reciprocal drift-deficit frequency theta_n in the BV infinite-activity survival-null argument.
-- source:
--   Accepted nonnegative_uniform_time_grid_exists; semifield eq_div_iff.

import Theorems.Thm_AvramDividend_Classical_nonnegative_uniform_time_grid_exists
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.NormNum

open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.nonnegative_uniform_time_grid_with_reciprocal_width
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ (ts : ℕ → ℝ≥0) (δ : ℝ≥0),
      ts 0 = 0 ∧ ts N = T ∧
      (∀ k : ℕ, k < N → ts k ≤ ts (k + 1)) ∧
      (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
      (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
      δ = T / (N : ℝ≥0) := by sorry
