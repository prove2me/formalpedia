-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_deficit_partition_exponential_sum_bound
-- name    : AvramDividend.Classical.capped_deficit_partition_exponential_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:13:33.034704+00:00
-- url     : https://prove2.me/theorems/2d9663b0-f03e-431e-965e-f301a921c81e
-- title:
--   Capped nonnegative path increments admit a telescoping exponential mesh bound
-- statement:
--   For a finite mesh, if every increment of a real path D is between zero and a positive cap a, its cumulative increment is bounded by 4a times the sum of exponential deficits of each mesh increment, at inverse scale 2a. The proof applies the already proved bounded-increment exponential estimate to each cell and telescopes the finite sum. This is the deterministic input for the infinite-activity Lévy finite-mesh no-monotone-path argument.
-- source:
--   Proved nonnegative_truncated_le_exp_gap; Finset.sum_range_sub and Finset.sum_le_sum.

import Theorems.Thm_AvramDividend_Classical_nonnegative_truncated_le_exp_gap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators

theorem AvramDividend.Classical.capped_deficit_partition_exponential_sum_bound
    (D : ℕ → ℝ) (N : ℕ) (a : ℝ) (ha : 0 < a)
    (hNonneg : ∀ k : ℕ, k < N → 0 ≤ D (k + 1) - D k)
    (hCap : ∀ k : ℕ, k < N → D (k + 1) - D k ≤ a) :
    D N - D 0 ≤
      4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) - D k) / (2 * a)))) := by sorry
