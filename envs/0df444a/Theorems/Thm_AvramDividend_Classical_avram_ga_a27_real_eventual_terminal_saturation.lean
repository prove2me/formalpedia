-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_real_eventual_terminal_saturation
-- name    : AvramDividend.Classical.avram_ga_a27_real_eventual_terminal_saturation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:18:23.400891+00:00
-- url     : https://prove2.me/theorems/a048b312-164b-49fa-a0c0-8b11db10fdb0
-- title:
--   Original clipped terminal cell: every strictly earlier time eventually lies before the final mesh endpoint
-- statement:
--   If a clock r is strictly smaller than the finite horizon n, then for all sufficiently fine uniform meshes indexed by m, the last interior mesh endpoint m n/(m+1) is at least r. This isolates the terminal clipped cell to clocks exactly at the horizon.
-- source:
--   Original stopped Gaussian terminal spatial positive-part convergence proof dependency

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_ga_a27_real_eventual_terminal_saturation
    (r n : ℝ) (hn : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ) * n / ((m : ℝ) + 1) := by sorry
