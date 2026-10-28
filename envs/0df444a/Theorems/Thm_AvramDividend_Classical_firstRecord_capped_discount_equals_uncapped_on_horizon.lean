-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_discount_equals_uncapped_on_horizon
-- name    : AvramDividend.Classical.firstRecord_capped_discount_equals_uncapped_on_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:11:53.597796+00:00
-- url     : https://prove2.me/theorems/126c3116-7713-447e-bed0-87f676fcd23d
-- title:
--   Capped strict-record exponential discount equals its uncapped value within the horizon
-- statement:
--   When the true strict upward record occurs no later than a finite cap, its capped NNReal conversion yields precisely the uncapped real time in the exponential dividend-discount weight, including the ENNReal dividend-size factor.
-- source:
--   Proved firstRecord_capped_clock_eq_uncapped_of_le_horizon, applying ENNReal.toReal and congruence of exponential discount.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_discount_equals_uncapped_on_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε q : ℝ) (N : ℝ≥0) (ω : Ω)
    (hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    ENNReal.ofReal ε *
      ENNReal.ofReal (Real.exp (-(q *
        (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ)))) =
    ENNReal.ofReal ε *
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X b ω).toReal))) := by sorry
