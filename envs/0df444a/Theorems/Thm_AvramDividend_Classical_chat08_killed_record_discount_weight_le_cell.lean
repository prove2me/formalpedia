-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_killed_record_discount_weight_le_cell
-- name    : AvramDividend.Classical.chat08_killed_record_discount_weight_le_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:17:33.78506+00:00
-- url     : https://prove2.me/theorems/82975cb2-115a-4d0e-9dea-052a55d0894e
-- title:
--   A killed discounted first-record weight never exceeds its cell mass
-- statement:
--   For nonnegative discount q and nonnegative cell mass h, the killed discounted strict first-passage record payment is bounded pointwise by h, whether ruin intervenes before passage or the passage occurs. This supplies a uniform envelope for finite stopped first-record weights and helps control integrability and terminal cells in the pathwise renewal comparison.
-- source:
--   Real.exp_le_one_iff and ENNReal.ofReal monotonicity, with the official strict first-passage and reflected ruin clocks.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_killed_record_discount_weight_le_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c q h : ℝ)
    (hq : 0 ≤ q) (hh : 0 ≤ h) (ω : Ω) :
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0) ≤ ENNReal.ofReal h := by sorry
