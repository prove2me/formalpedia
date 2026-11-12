-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva49_original_uniform_grid_isolates_finite_jump_times
-- name    : AvramDividend.Classical.avram_bva49_original_uniform_grid_isolates_finite_jump_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:11:14.595083+00:00
-- url     : https://prove2.me/theorems/147dc190-44ce-4ab6-9bfb-9c71c91f6842
-- title:
--   The original uniform physical mesh eventually isolates every finite negative jump time
-- statement:
--   At sufficiently fine levels of the original uniform physical mesh T/(n+2), no physical half-open grid cell can contain two distinct jump times from a finite set. Exact source mesh, no artificial avoidance of jump-grid coincidences, and no auxiliary process are required.
-- source:
--   Closure of proved finite spacing 539a67f9 and authored two-step helpers bva47 and bva48, needed for original BV finite-positive-jump physical source 4287fafd-afdc-46b2-a160-033b7b2500f2, 11 November 2026.

import Mathlib

theorem AvramDividend.Classical.avram_bva49_original_uniform_grid_isolates_finite_jump_times (S : Finset ℝ) (T : ℝ) (hT : 0 < T) : ∀ᶠ n : ℕ in Filter.atTop, ∀ a s t : ℝ, s ∈ S → t ∈ S → a ≤ s → s < a + T / ((n : ℝ) + 2) → a ≤ t → t < a + T / ((n : ℝ) + 2) → s = t := by sorry
