-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_down_count_le_of_uniform_close
-- name    : AvramDividend.Classical.finite_grid_down_count_le_of_uniform_close
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:31:26.902587+00:00
-- url     : https://prove2.me/theorems/c6999ca4-f9f0-4a68-a048-06ba5c306e53
-- title:
--   Uniformly close paths preserve large downward grid counts with an explicit double-error threshold
-- statement:
--   If sample paths f and g differ by at most epsilon in absolute value at every time, each downward f-decrement larger than a+2epsilon implies a downward g-decrement larger than a. Therefore on any finite grid of pairs the number of f-decrements above the larger threshold is no more than the number of g-decrements above the smaller threshold. This deterministic uniform-approximation step is useful for comparing finite-annulus canonical Poisson step paths with their uniform-on-compact limits.
-- source:
--   Mathlib Finset.sum_le_sum and abs_le; canonical path analysis in LeanLevy/RandomMeasure/LevyJumpPath.lean

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_grid_down_count_le_of_uniform_close
    (grid : Finset (ℝ≥0 × ℝ≥0)) (a ε : ℝ)
    (f g : ℝ≥0 → ℝ)
    (hclose : ∀ t, |f t - g t| ≤ ε) :
    (∑ ij ∈ grid,
      if f ij.2 - f ij.1 < -(a + 2 * ε) then (1 : ℕ) else 0) ≤
    ∑ ij ∈ grid,
      if g ij.2 - g ij.1 < -a then (1 : ℕ) else 0 := by sorry
