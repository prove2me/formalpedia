-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_halfopen_cell_locator
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_halfopen_cell_locator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:11:22.182989+00:00
-- url     : https://prove2.me/theorems/72d32a4b-b0ee-4b5a-a62e-619253cf39dd
-- title:
--   Every positive source time belongs to a uniform right-closed finite-horizon grid cell
-- statement:
--   For any T>0, u in (0,T], and integer n, there is a cell index i<=n with i*T/(n+1)<u<=(i+1)*T/(n+1). The construction uses ceil((n+1)u/T)-1 and preserves left-open right-closed endpoints, including jump times exactly on the grid. This is the arithmetic basis for actual source jump grid capture with no intensity, Poisson or finite-activity assumptions.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_halfopen_cell_locator
    (T u : ℝ≥0) (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (n : ℕ) :
    ∃ i : ℕ, i ≤ n ∧
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) := by sorry
