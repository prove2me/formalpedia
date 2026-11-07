-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_uniform_physical_grid_endpoints
-- name    : AvramDividend.Classical.avram_bv_strict6_uniform_physical_grid_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:04:33.695602+00:00
-- url     : https://prove2.me/theorems/f0a545e6-b969-4349-89fe-fa27214360e7
-- title:
--   Exact original BV physical uniform-grid endpoints and monotonicity
-- statement:
--   For any positive deterministic horizon T, construct the explicit genuine uniform physical grid u n i = T*i/(n+2), with nonnegative times, u n 0 = 0, last time u n (n+1) = T - T/(n+2), and monotone consecutive times. These are precisely the path-independent geometry hypotheses of the original stopped-cell witness 2bc848f9, and the uniform mesh is suitable for physical C1 mesh approximations.

import Mathlib
open Filter Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_uniform_physical_grid_endpoints
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by sorry
