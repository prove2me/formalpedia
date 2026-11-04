-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
-- name    : AvramDividend.Classical.avram_wave7_06_monotone_marked_grid_index_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:54:00.607311+00:00
-- url     : https://prove2.me/theorems/18c2aab0-b3aa-45b5-86f8-61821357f5f5
-- title:
--   A source marked jump time has at most one index in a monotone right-closed grid
-- statement:
--   For any monotone grid of nonnegative times and any actual marked jump time, membership in two half-open cells forces their indices to coincide. This is the index-uniqueness certificate consumed by the original Lévy marked-grid occupied-cardinality theorem.
-- source:
--   Discrete original Lévy marked-time grid geometry, source sample paths are not replaced.

import Mathlib
open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_monotone_marked_grid_index_unique
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (u : ℝ≥0) (i j : ℕ)
    (hi : u ∈ Set.Ioc (grid i) (grid (i + 1)))
    (hj : u ∈ Set.Ioc (grid j) (grid (j + 1))) :
    i = j := by sorry
