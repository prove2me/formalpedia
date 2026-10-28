-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_before_horizon_iff_dense_grid_of_right_negative_persistence
-- name    : AvramDividend.Classical.negative_before_horizon_iff_dense_grid_of_right_negative_persistence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:29:41.113762+00:00
-- url     : https://prove2.me/theorems/a0a6a940-d5e9-4bc0-9ae5-6e7ec345c645
-- title:
--   A dense countable time grid detects every negative observation of a right-negative-persistent path
-- statement:
--   Let a real-valued nonnegative-time path have the right-neighbourhood property that whenever f(t)<0 it remains negative for some nonzero right interval. For any countable time schedule dense in every nonempty interval, a strictly negative observation before a horizon ε exists if and only if such an observation exists at one of the countably selected grid times before ε. Right continuity implies this persistence property; that analytic implication is left separate. This bridges all-time downward regularity to the countable product-measurable event used in the strong Markov transfer.
-- source:
--   Pathwise right-continuity and countable dense-time determination of open threshold crossing for càdlàg Lévy paths. Supports excursion-height atomlessness, Kuznetsov, Kyprianou and Rivero (2013), Section 2.3.

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.OrderClosed

open Set
open scoped NNReal

theorem AvramDividend.Classical.negative_before_horizon_iff_dense_grid_of_right_negative_persistence
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (f : ℝ≥0 → ℝ)
    (hnegOpen : ∀ t : ℝ≥0, f t < 0 →
      ∃ u : ℝ≥0, t < u ∧
        ∀ s : ℝ≥0, t ≤ s → s < u → f s < 0)
    (ε : ℝ≥0) :
    (∃ t : ℝ≥0, t < ε ∧ f t < 0) ↔
      (∃ m : ℕ, times m < ε ∧ f (times m) < 0) := by sorry
