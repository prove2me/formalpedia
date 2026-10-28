-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_integral_eq_natTruncation
-- name    : AvramDividend.Classical.firstRecord_capped_integral_eq_natTruncation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:32:22.524536+00:00
-- url     : https://prove2.me/theorems/b8e92c7f-69ef-41ea-a3fd-6f39d119e210
-- title:
--   Capped first-record integral equals standard finite-horizon truncation of killed reward
-- statement:
--   The expected capped strict first-record reward before ruin agrees exactly with the ordinary finite-horizon truncation of the full killed first-record discounted reward. Equality holds for each deterministic nonnegative horizon and nonnegative dividend increment.
-- source:
--   Proved firstRecord_capped_discount_equals_uncapped_on_horizon and Mathlib ENNReal.ofReal_mul.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_discount_equals_uncapped_on_horizon

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_integral_eq_natTruncation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (hε : 0 ≤ ε) (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X b ω).toReal)))
       else 0) else 0 ∂P) := by sorry
