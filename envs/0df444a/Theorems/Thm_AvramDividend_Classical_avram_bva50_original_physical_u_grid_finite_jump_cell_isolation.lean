-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
-- name    : AvramDividend.Classical.avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:31:39.237994+00:00
-- url     : https://prove2.me/theorems/a1e08404-3508-4d95-aba1-5d26dd576ab4
-- title:
--   Actual original uniform physical grid cells eventually isolate finite jump times
-- statement:
--   For the exact physical uniform-grid function u used by the original BV source theorem and any finite set of actual original jump times, each half-open cell from u n i to u n (i+1) contains at most one jump for all sufficiently fine grids, uniformly over i.
-- source:
--   Immediate application of Proved 147dc190-44ce-4ab6-9bfb-9c71c91f6842 to huniform in the source-exact physical BV finite-mark theorem 4287fafd-afdc-46b2-a160-033b7b2500f2, 11 November 2026.

import Mathlib
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bva50_original_physical_u_grid_finite_jump_cell_isolation (S : Finset ℝ) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) : ∀ᶠ n : ℕ in Filter.atTop, ∀ i : ℕ, ∀ s t : ℝ, s ∈ S → t ∈ S → (u n i : ℝ) ≤ s → s < (u n (i + 1) : ℝ) → (u n i : ℝ) ≤ t → t < (u n (i + 1) : ℝ) → s = t := by sorry
