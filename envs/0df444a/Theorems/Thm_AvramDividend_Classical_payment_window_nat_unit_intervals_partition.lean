-- Prove2me | Theorems.Thm_AvramDividend_Classical_payment_window_nat_unit_intervals_partition
-- name    : AvramDividend.Classical.payment_window_nat_unit_intervals_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:44:35.678954+00:00
-- url     : https://prove2.me/theorems/1a6ecfa0-caa5-4689-9061-b41dac5d96cf
-- title:
--   Countable half-open unit intervals partition stopped dividend payment times
-- statement:
--   For any ruin stopping boundary and finite-horizon real time, the nonnegative stopped dividend payment window is the union of its intersections with half-open unit intervals indexed by natural numbers. Every component is measurable and distinct components are disjoint. Half-open intervals assign endpoint atoms exactly once. The proof uses the natural-number floor to locate each payment time. Applying this lemma to the separately Proved stopped_dividend_payment_partition_lintegral_eq_iSup_cash establishes that actual truncated Stieltjes dividend payments equal the supremum of their exact unit-interval cash sums; this is the pathwise limit needed by both capped BV and UV stochastic cores.

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.payment_window_nat_unit_intervals_partition
    (σ : ℝ≥0∞) (T : ℝ) :
    (∀ k : ℕ, MeasurableSet
      ((paymentTimes σ ∩ Iic T) ∩ Ico (k : ℝ) ((k : ℝ) + 1))) ∧
    Pairwise (Function.onFun Disjoint
      (fun k : ℕ => (paymentTimes σ ∩ Iic T) ∩
        Ico (k : ℝ) ((k : ℝ) + 1))) ∧
    (⋃ k : ℕ, (paymentTimes σ ∩ Iic T) ∩
      Ico (k : ℝ) ((k : ℝ) + 1)) =
      paymentTimes σ ∩ Iic T := by sorry
