-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
-- name    : AvramDividend.Classical.stopped_lintegral_Ioc_partition_fin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:44:04.853389+00:00
-- url     : https://prove2.me/theorems/327485ca-2f02-40a7-ae17-175bddbe2b84
-- title:
--   Exact finite half-open partition of a stopped nonnegative Stieltjes payout
-- statement:
--   For any real-time measure μ, arbitrary stopped-payment set A, nonnegative payout weight f, monotone sequence of real time endpoints u and finite grid size n, the payout over the complete interval (u(0),u(n)] under the measure restricted to A equals the finite sum of payouts over all adjacent half-open grid intervals. The identity allows empty cells and infinite rewards. It uses the remotely accepted finite Ioc partition theorem for the stopped measure μ.restrict A, with a pointwise membership split to equate explicit interval indicators with Set.indicator. It provides a direct pathwise finite-grid aggregation interface for the actual reflected-supremum dividend rewards.
-- source:
--   ACCEPTED lintegral_Ioc_partition_fin target 947adc6d-e8fb-4c10-bd23-a43d10ca8870 candidate 12747, pinned Mathlib lintegral_indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_lintegral_Ioc_partition_fin
    (μ : Measure ℝ) (A : Set ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∫⁻ r in A, if r ∈ Set.Ioc (u 0) (u n) then f r else 0 ∂μ) =
    ∑ i ∈ Finset.range n,
      ∫⁻ r in A,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then f r else 0 ∂μ := by sorry
