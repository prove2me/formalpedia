-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_countable_weighted_first_occurrence
-- name    : AvramDividend.Classical.avram_bv_jump8_countable_weighted_first_occurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:23:45.540371+00:00
-- url     : https://prove2.me/theorems/27229df0-e052-4d29-b258-691438e1dce0
-- title:
--   Weighted countable-cover sum equals the first-occurrence deduplicated series
-- statement:
--   For any countable sequence whose range covers a set of times, and any extended nonnegative weight on times, summing weights over the set equals summing over the first appearance of each covered element. The identity works for infinite sums, repeated candidates and arbitrary zero weights, and requires no measurability or stochastic hypotheses.
-- source:
--   Weighted extension of Proved 2880a35d first-occurrence count. Establish the bijection between the first-index subtype and the set of covered times and use ENNReal Equiv.tsum_eq. Key to b50e56f2 intrinsic weighted original marked-jump path extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_countable_weighted_first_occurrence
    (time : ℕ → ℝ≥0) (S : Set ℝ≥0)
    (hCover : S ⊆ Set.range time)
    (f : ℝ≥0 → ℝ≥0∞) :
    (∑' u : S, f (u : ℝ≥0)) =
      ∑' k : ℕ,
        if time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
        then f (time k) else 0 := by sorry
