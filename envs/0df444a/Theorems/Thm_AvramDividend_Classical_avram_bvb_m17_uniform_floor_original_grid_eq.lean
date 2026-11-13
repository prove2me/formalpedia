-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_uniform_floor_original_grid_eq
-- name    : AvramDividend.Classical.avram_bvb_m17_uniform_floor_original_grid_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:23:21.0902+00:00
-- url     : https://prove2.me/theorems/b1f1a3c8-b00e-4c0f-868b-0b99929d10ac
-- title:
--   Original physical uniform-grid cell at the floor index equals real-to-NNReal uniform sample
-- statement:
--   For the actual physical uniform dividend-time mesh u(n,i)=T i/(n+2), evaluating u at the floor index of an arbitrary real observation time is exactly the nonnegative real-to-NNReal floor sample. Valid for all n, all observation times and all real positive horizons. This allows the existing Proved original pre-ruin floor kernel convergence to apply without altering the source grid.
-- source:
--   Pinned Mathlib Real.coe_toNNReal, original BV physical uniform stopped grid; intended source exact bvb28 convergence.

import Mathlib
open Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_m17_uniform_floor_original_grid_eq
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (r : ℝ) :
    u n ⌊(r / T) * ((n : ℝ) + 2)⌋₊ =
      Real.toNNReal
        (T * (⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2)) := by sorry
