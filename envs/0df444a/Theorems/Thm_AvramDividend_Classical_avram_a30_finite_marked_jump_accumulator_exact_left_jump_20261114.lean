-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114
-- name    : AvramDividend.Classical.avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:23:06.110189+00:00
-- url     : https://prove2.me/theorems/6791bb4e-bc25-407a-9a4b-271ae2719e2b
-- title:
--   Finite causal physical marked-jump accumulator has exact jump equal to the mark at supported time
-- statement:
--   For any finite collection of times with real marks, the right-continuous causal jump sum at time t minus the sum of marks strictly before t equals the mark at t when t belongs to the support and zero otherwise.
-- source:
--   Pinned Mathlib Finset.sum_sub_distrib and indicator sum.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A finite causal marked-jump accumulator has jump equal to its mark at each supported time. -/

theorem AvramDividend.Classical.avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114 (S : Finset ℝ≥0) (a : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (∑ u ∈ S, if u ≤ t then a u else 0) -
      (∑ u ∈ S, if u < t then a u else 0) =
      if t ∈ S then a t else 0 := by sorry
