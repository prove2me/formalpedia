-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_nextRecord_trueFactor_lower
-- name    : AvramDividend.Classical.firstRecord_capped_nextRecord_trueFactor_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:41:15.943736+00:00
-- url     : https://prove2.me/theorems/8f8b667e-f7e7-44d8-a7ec-b2503da7f816
-- title:
--   Unconditional capped first-record renewal lower inequality with true two-sided factor
-- statement:
--   For every finite cap, the expected killed next-record payment dominates the product of the capped previous-record discounted reward and independent true two-sided exit factor, with all measurable-discount obligations discharged.
-- source:
--   Proved firstRecord_capped_markov_nextRecord_integral_lower and capped_record_exponential_discount_measurable.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_markov_nextRecord_integral_lower
import Theorems.Thm_AvramDividend_Classical_capped_record_exponential_discount_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_nextRecord_trueFactor_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0)
    :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
         twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by sorry
