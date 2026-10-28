-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
-- name    : AvramDividend.Classical.stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:30:06.869776+00:00
-- url     : https://prove2.me/theorems/dca46947-a267-40f8-9fe4-2ccfc9f01de8
-- title:
--   A bounded Stieltjes CDF vanishing at negative infinity generates a finite measure
-- statement:
--   Any monotone right-continuous real Stieltjes function that is zero on every negative input and globally bounded above by one generates a finite Stieltjes measure. Its limits at both infinities exist as finite real numbers, and the measure total mass is finite, possibly strictly less than one.
-- source:
--   Use eventual equality to zero at negative infinity, the pinned `tendsto_atTop_ciSup` monotone convergence theorem with BddAbove(range S), and pinned `StieltjesFunction.isFiniteMeasure`. This establishes that the limiting Esscher reflected-infimum distribution measure is genuinely finite without asserting its total mass equals one.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.Defs
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0)
    (hbound : ∀ x : ℝ, S x ≤ 1) :
    IsFiniteMeasure S.measure := by sorry
