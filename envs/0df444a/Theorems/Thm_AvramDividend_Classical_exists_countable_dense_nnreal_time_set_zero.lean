-- Prove2me | Theorems.Thm_AvramDividend_Classical_exists_countable_dense_nnreal_time_set_zero
-- name    : AvramDividend.Classical.exists_countable_dense_nnreal_time_set_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:29:26.328593+00:00
-- url     : https://prove2.me/theorems/cced1858-0295-4c31-997e-c860421155da
-- title:
--   There exists a countable dense subset of nonnegative real time containing zero
-- statement:
--   There is a countable dense subset S of the time domain ℝ≥0 that contains its bottom element zero. Apply Mathlib's Dense.exists_countable_dense_subset_bot_top to the whole separable space ℝ≥0. This eliminates the extrinsic dense sampling set assumption from the accepted reflected continuous-time prefix supremum adaptedness theorem and from the forthcoming true capped first closed-level hitting stopping-time theorem. It is an existence theorem only: the family can be chosen once and used uniformly for all time horizons and thresholds.
-- source:
--   Pinned Mathlib.Topology.Bases Dense.exists_countable_dense_subset_bot_top; Mathlib.Order.BoundedOrder.Basic isBot_bot.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bases
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.BoundedOrder.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.exists_countable_dense_nnreal_time_set_zero :
    ∃ S : Set ℝ≥0,
      S.Countable ∧ Dense S ∧ (0 : ℝ≥0) ∈ S := by sorry
