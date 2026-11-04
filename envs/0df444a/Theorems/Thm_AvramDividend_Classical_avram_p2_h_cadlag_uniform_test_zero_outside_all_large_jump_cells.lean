-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:17:44.11731+00:00
-- url     : https://prove2.me/theorems/5d0e7247-357e-4395-86fb-82f08e14d8a3
-- title:
--   Separated test functions vanish off cells of all large genuine jumps
-- statement:
--   For any test vanishing near zero and a finite set covering every actual jump above that threshold, the full sufficiently fine uniform grid test sum is supported on cells selected by the finite jump set. Uses no-spurious-large-cell compactness and uniqueness of right-closed cell locators.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_right_closed_grid_cell_locator_unique

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (S : Finset ℝ≥0)
    (hS : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ S)
    (j : ℝ≥0 → ℕ → ℕ)
    (hj : ∀ u ∈ S, ∀ n : ℕ,
      j u n ≤ n ∧
      (j u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ (((j u n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.range (n + 1),
        i ∉ S.image (fun u => j u n) →
        f (Y ((((i + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) = 0 := by sorry
