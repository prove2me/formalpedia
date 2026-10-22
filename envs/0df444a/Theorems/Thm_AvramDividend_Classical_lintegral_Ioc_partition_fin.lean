-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin
-- name    : AvramDividend.Classical.lintegral_Ioc_partition_fin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:23:48.455568+00:00
-- url     : https://prove2.me/theorems/947adc6d-e8fb-4c10-bd23-a43d10ca8870
-- title:
--   Finite monotone time-grid Stieltjes reward equals sum of its half-open cell rewards
-- statement:
--   For an arbitrary real-time measure, nonnegative extended-real payout weight and nondecreasing sequence of real times u(n), the entire Stieltjes payout on (u(0),u(n)] equals the sum of the payouts on the adjacent half-open cells (u(i),u(i+1)] for i<n. The result is exact even for infinite total reward and allows coincident grid times; empty cells contribute zero. This is the finite-record-grid partition theorem needed to add the proved first-record h-cell dividend inequalities over successive passage levels without double-counting record-time boundary dividends.
-- source:
--   Dependency-gated lintegral_Ioc_adjacent_add authoring request 851ccb10-9c2c-4125-b0e2-72c9e18304dc; pinned Mathlib Finset.sum_range_succ and Nat arithmetic; exact finite induction.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.lintegral_Ioc_partition_fin
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∫⁻ r in Set.Ioc (u 0) (u n), f r ∂μ) =
    ∑ i ∈ Finset.range n,
      ∫⁻ r in Set.Ioc (u i) (u (i + 1)), f r ∂μ := by sorry
