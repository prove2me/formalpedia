-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:24:53.452377+00:00
-- url     : https://prove2.me/theorems/c78e55dd-1e17-493f-8be8-c63af8f51cba
-- title:
--   Canonical physical time grid covers every bounded stopped clock at each mesh level
-- statement:
--   For the original canonical uniform physical mesh with m(j)=(n+1)(j+1), any stopped NNReal clock at most n is covered for every j, strengthening an already proved eventual coverage bound. This supplies the all-indices hcover premise of the original all-cap closed Stieltjes cash estimate for the true stopped event.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    t ≤ (((n + 1) * (j + 1) : ℕ) : ℝ≥0) /
      (((j + 1 : ℕ) : ℝ≥0)) := by sorry
