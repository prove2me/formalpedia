-- Prove2me | Theorems.Thm_AvramDividend_Classical_recordPartition_finite_cover_iff
-- name    : AvramDividend.Classical.recordPartition_finite_cover_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:47:34.497622+00:00
-- url     : https://prove2.me/theorems/3f2b95f1-5c84-47e0-a362-61f1639d5806
-- title:
--   Finite consecutive record-level half-open cells exactly cover the total interval
-- statement:
--   For a monotone sequence of real partition levels, a point lies strictly above the initial level and at or below the final level exactly when it belongs to one of the consecutive half-open cells, with an index strictly smaller than the partition length. This deterministic characterisation supplies finite union coverage needed for Stieltjes payout decomposition, retaining the strict-left and weak-right endpoint convention.
-- source:
--   Elementary induction on the number of monotone partition intervals, using the order properties of ℝ and ℕ. No stochastic assumptions or unpublished theorems.

import Mathlib.MeasureTheory.Measure.Stieltjes

theorem AvramDividend.Classical.recordPartition_finite_cover_iff
    (u : ℕ → ℝ) (hu : Monotone u)
    (n : ℕ) (x : ℝ) :
    (u 0 < x ∧ x ≤ u n) ↔
      ∃ i : ℕ, i < n ∧ u i < x ∧ x ≤ u (i + 1) := by sorry
