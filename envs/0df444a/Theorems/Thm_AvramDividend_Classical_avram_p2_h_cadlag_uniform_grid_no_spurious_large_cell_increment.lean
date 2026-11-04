-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:01:17.228145+00:00
-- url     : https://prove2.me/theorems/ad355abc-80df-4d02-a64d-35623fb11d68
-- title:
--   Original uniform-grid large cells eventually contain actual càdlàg jumps
-- statement:
--   For a positive NNReal horizon and any real càdlàg path, every sufficiently fine right-closed uniform-grid cell with large increment contains a same-threshold genuine jump. Handles the initial time, the terminal endpoint and an exactly aligned jump using the right-closed convention.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_right_closed_cell_real_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ, i ≤ n →
      ρ ≤ |Y ((((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) -
        Y (((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))| →
      ∃ t : ℝ≥0,
        ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < t ∧
        t ≤ (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
        ρ ≤ |Y t - Function.leftLim Y t| := by sorry
