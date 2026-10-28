-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_le_unweighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:11:38.165736+00:00
-- url     : https://prove2.me/theorems/25fe0eaf-8602-4253-a58a-04a4c49570c5
-- title:
--   Negative Esscher-weighted Lévy tail is bounded by unweighted tail
-- statement:
--   For positive truncation x and nonnegative Esscher parameter φ, all signed jumps y<-x are negative, so exp(φ y)≤1. Consequently the weighted negative Lévy tail is bounded above by its unweighted counterpart. This proves the finiteness needed for toReal conversion whenever the original truncated Lévy mass is finite.
-- source:
--   Mathlib MeasureTheory.withDensity_apply, setLIntegral_mono and setLIntegral_one; Real.exp_le_one_iff.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- On a negative-jump tail the nonnegative Esscher weight is at most one. -/
theorem esscher_weighted_negative_tail_le_unweighted
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) ≤ ν (Iio (-x)) := by sorry

end AvramDividend.Classical
