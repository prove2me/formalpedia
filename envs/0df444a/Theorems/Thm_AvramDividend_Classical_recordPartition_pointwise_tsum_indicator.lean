-- Prove2me | Theorems.Thm_AvramDividend_Classical_recordPartition_pointwise_tsum_indicator
-- name    : AvramDividend.Classical.recordPartition_pointwise_tsum_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:12:10.802716+00:00
-- url     : https://prove2.me/theorems/4a3b15b9-0114-428f-b6d0-cfffd4087c92
-- title:
--   Partition-of-unity identity for countable half-open cofinal monotone record intervals
-- statement:
--   For any nondecreasing cofinal real sequence, precisely one consecutive half-open interval contains any point above the initial level, and no interval contains a point at or below it. Thus the sum over all natural indices of the indicator times any extended-nonnegative constant equals that constant on the final half-line and zero elsewhere. The proof uses the remotely proved countable cover and ordered interval disjointness, and the pinned tsum_eq_single lemma. This is the pointwise identity required to turn a sum of interval Stieltjes rewards into the genuine integral over the covered time set.
-- source:
--   Remotely Proved recordPartition_Ioc_disjoint target 26b30a5d-eb69-4fbf-b1ab-aa17bfbb5d8e; dependency-gated recordPartition_countable_cover_iff submitted for publication 2a7b9d7f-8dee-4862-9254-f92e9165058a; pinned tsum_eq_single, Set.disjoint_left, lt_or_gt_of_ne.

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_AvramDividend_Classical_recordPartition_Ioc_disjoint
import Theorems.Thm_AvramDividend_Classical_recordPartition_countable_cover_iff

open Set
open scoped ENNReal

theorem AvramDividend.Classical.recordPartition_pointwise_tsum_indicator
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (r : ℝ) (c : ℝ≥0∞) :
    (∑' i : ℕ,
      if r ∈ Set.Ioc (u i) (u (i + 1)) then c else 0) =
      if u 0 < r then c else 0 := by sorry
