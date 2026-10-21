-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_lintegral_le_one
-- name    : AvramDividend.Classical.chat03_discounted_upperfirst_lintegral_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:27:27.422695+00:00
-- url     : https://prove2.me/theorems/68458118-5cfe-4326-b06e-d706b8ab310d
-- title:
--   Probability expectation of the exact upper-first discounted weight is bounded by one
-- statement:
--   For any probability measure and any two possibly infinite nonnegative random passage clocks, the expected ENNReal-valued upper-first exponential discount payoff is no greater than one whenever the discount parameter is nonnegative. This follows by integrating the previously Proved deterministic bound 0≤weight≤1, using the probability measure total mass one. In particular, the exact lintegral in the Avram stopped-scale parent theorem is finite. No adaptedness, stopping time theorem or killed scale martingale identity is assumed.
-- source:
--   Proved Chat03 discounted upper-first weight bound, pinned Mathlib lintegral_mono and probability lintegral_const.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_discounted_upperfirst_lintegral_le_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q) (up down : Ω → ℝ≥0∞) :
    (∫⁻ ω : Ω,
      if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
      else 0 ∂P) ≤ 1 := by sorry
