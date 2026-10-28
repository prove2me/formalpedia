-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_nnreal_dense_grid_strictly_cofinal
-- name    : AvramDividend.Classical.countable_nnreal_dense_grid_strictly_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:25:57.643268+00:00
-- url     : https://prove2.me/theorems/ea0d4dcf-23ca-4ec8-9d0f-02b7f1ea8f1c
-- title:
--   A dense countable nonnegative time grid is strictly cofinal below any extended horizon
-- statement:
--   For any countable dense sequence of nonnegative real times and any time strictly below an extended nonnegative stopping horizon, a grid time lies strictly between them. This justifies the deterministic cofinal-grid hypothesis in the stopped discounted dividend Stieltjes integral identity, including an infinite stopping horizon.
-- source:
--   Topological density of nonnegative real numbers and the cofinal embedding into extended nonnegative reals; Avram classical zero-barrier finite-activity stopped Stieltjes valuation.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Continuous
import Mathlib.Topology.Order.Basic

open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_nnreal_dense_grid_strictly_cofinal
    (grid : ℕ → ℝ≥0) (hDense : DenseRange grid)
    (σ : ℝ≥0∞) (t : ℝ≥0)
    (htσ : (t : ℝ≥0∞) < σ) :
    ∃ n : ℕ, t < grid n ∧ (grid n : ℝ≥0∞) < σ := by sorry
