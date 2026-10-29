-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_mesh_grid_calibration
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_bv_mesh_grid_calibration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:25:26.284595+00:00
-- url     : https://prove2.me/theorems/aee42db8-7cb1-41d9-a749-c374d404bc84
-- title:
--   Exact uniform-grid and Laplace calibration for physical BV drift-deficit bounds
-- statement:
--   For any strictly positive physical drift d, positive nonnegative-real horizon T and a positive integer mesh count N large enough that 2dT≤N, the canonical uniform mesh δ=T/N reaches T, has constant positive spacing, stays within the horizon, and its exponential test parameter 1/(2dδ) is at least one. Exact mass coefficient and exponent products are 4dT and 1/(2d), respectively. This real/NNReal geometry is the missing deterministic calibration in the accepted source-specific infinite-activity BV Lévy strict-survival mesh estimate; the theorem makes no stochastic assumption and does not claim the eventual survival identity itself.

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_bv_mesh_grid_calibration
    (d : ℝ) (hd : 0 < d)
    (T : ℝ≥0) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N)
    (hLarge : 2 * d * (T : ℝ) ≤ (N : ℝ)) :
    (let δ : ℝ≥0 := T / (N : ℝ≥0)
     let ts : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
     let a : ℝ := d * (δ : ℝ)
     0 < a ∧
     ts N = T ∧
     (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
     (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
     1 ≤ 1 / (2 * a) ∧
     (δ : ℝ) * (1 / (2 * a)) = 1 / (2 * d) ∧
     4 * a * (N : ℝ) = 4 * d * (T : ℝ)) := by sorry
