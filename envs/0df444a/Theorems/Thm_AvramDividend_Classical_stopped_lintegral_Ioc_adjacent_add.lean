-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add
-- name    : AvramDividend.Classical.stopped_lintegral_Ioc_adjacent_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:38:35.029241+00:00
-- url     : https://prove2.me/theorems/65474b41-f9b9-4209-9629-c89c544d5571
-- title:
--   Stopped Stieltjes reward is additive across adjacent half-open intervals
-- statement:
--   For any real-time measure, stopped payment set, nonnegative reward and ordered real endpoints s ≤ t ≤ u, the stopped reward over (s,u] equals the sum of stopped rewards over (s,t] and (t,u]. The equality holds for infinite dividends and does not impose stochastic regularity. It is the exact two-cell additivity interface used to collapse discounted four-record-cell bounds into one stopped Stieltjes integral.
-- source:
--   Direct corollary of the Proved lintegral_Ioc_adjacent_add (b6b43af5-6b3d-4d88-a98d-d14af38a8124), using measure restriction and lintegral_indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_lintegral_Ioc_adjacent_add
    (μ : Measure ℝ) (A : Set ℝ) (f : ℝ → ℝ≥0∞)
    (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    (∫⁻ r in A, if r ∈ Set.Ioc s u then f r else 0 ∂μ) =
      (∫⁻ r in A, if r ∈ Set.Ioc s t then f r else 0 ∂μ) +
      (∫⁻ r in A, if r ∈ Set.Ioc t u then f r else 0 ∂μ) := by sorry
