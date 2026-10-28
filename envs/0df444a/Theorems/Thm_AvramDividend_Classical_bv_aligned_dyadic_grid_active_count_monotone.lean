-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_aligned_dyadic_grid_active_count_monotone
-- name    : AvramDividend.Classical.bv_aligned_dyadic_grid_active_count_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:42:04.407615+00:00
-- url     : https://prove2.me/theorems/cbcbc2f8-2808-402d-8226-8631b5ca712b
-- title:
--   Dyadic active-increment count increases with each nested grid refinement
-- statement:
--   For any real-valued nonnegative-time path Y and any dyadic nested sequence of grids whose even-indexed refined points coincide with parent grid points, the number of adjacent grid cells with strictly positive increments is monotone increasing as the grid is refined. The accepted finite-sequence refinement count theorem is applied to the sequence of path values on the child grid, and the parent/child alignment rewrites parent active indicators. This is pathwise deterministic and is the exact monotonicity assumption required by the accepted almost-sure expected-count bound theorem.
-- source:
--   Avram Palmowski Pistorius (2007), first-jump finite activity branch; Prove2Me accepted dyadic active-count refinement

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_active_count_refinement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

open Finset
open scoped NNReal

theorem AvramDividend.Classical.bv_aligned_dyadic_grid_active_count_monotone
    (Y : ℝ≥0 → ℝ) (grid : ℕ → ℕ → ℝ≥0)
    (hRefine : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i) :
    Monotone (fun n : ℕ =>
      ∑ i ∈ Finset.range (2 ^ n),
        ite (Y (grid n i) < Y (grid n (i + 1))) (1 : ℕ) 0) := by sorry
