-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a31_physical_jump_accumulator_horizon_consistency_20261114
-- name    : AvramDividend.Classical.avram_a31_physical_jump_accumulator_horizon_consistency_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:29:10.156311+00:00
-- url     : https://prove2.me/theorems/206e314b-f756-4393-a174-2227ef60d5f1
-- title:
--   Finite causal marked jump accumulators from nested horizons agree throughout the earlier horizon
-- statement:
--   Given finite collections of physical nonzero jump marks supported within nested time horizons, their causal marked sums agree at every time within the smaller horizon, because added future jumps contribute zero.
-- source:
--   Pinned Mathlib Finset.sum_subset and order properties of nonnegative time.

import Mathlib
open Set Filter Topology
open scoped NNReal BigOperators
noncomputable section

/-- Finite physical marked jump accumulators are compatible across nested time horizons. -/

theorem AvramDividend.Classical.avram_a31_physical_jump_accumulator_horizon_consistency_20261114
    (a : ℝ≥0 → ℝ) (T U : ℝ≥0) (hTU : T ≤ U)
    (S R : Finset ℝ≥0)
    (hS : ∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ a u ≠ 0)
    (hR : ∀ u, u ∈ R ↔ 0 < u ∧ u ≤ U ∧ a u ≠ 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑ u ∈ S, if u ≤ t then a u else 0) =
      (∑ u ∈ R, if u ≤ t then a u else 0) := by sorry
