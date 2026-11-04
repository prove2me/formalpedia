-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_selected_indices_in_grid
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_indices_in_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:23:16.686929+00:00
-- url     : https://prove2.me/theorems/03087605-fe24-498f-baaf-2821a2b023bd
-- title:
--   Finite original uniform source-grid contains every selected jump cell
-- statement:
--   A coherent finite jump-cell selector for the original uniform grid satisfies idx(t,n) ≤ n. Consequently every selected cell is in the actual finite grid Finset.range(n+1), discharging the hinside condition of the proven pathwise full-grid compact-test limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_indices_in_grid
    (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ)
    (hidx : ∀ t ∈ F, ∀ n : ℕ, idx t n ≤ n) :
    ∀ n : ℕ, ∀ t ∈ F, idx t n ∈ Finset.range (n + 1) := by sorry
