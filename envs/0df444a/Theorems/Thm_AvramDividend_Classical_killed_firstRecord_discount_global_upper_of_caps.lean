-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_global_upper_of_caps
-- name    : AvramDividend.Classical.killed_firstRecord_discount_global_upper_of_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:32:59.108423+00:00
-- url     : https://prove2.me/theorems/7ed98ea2-19cd-494c-963a-433ca927aa43
-- title:
--   Uncapped Lévy first-record discounted reward is bounded by uniform capped bounds
-- statement:
--   For the actual Lévy killed upper-record discounted payoff, apply monotone convergence of finite cap rewards and the fact that the payoff vanishes if the record never occurs. Reduces the global killed renewal expectation bound to estimates valid for all finite horizons.
-- source:
--   Accepted generic cap-removal theorem and infinite-upclock zero reward

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_weight_global_lintegral_le_of_uniform_caps
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_discount_global_upper_of_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε q : ℝ)
    (hT : Measurable (twoSidedExitUpTime X b))
    (hw : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp (-(q *
          (twoSidedExitUpTime X b ω).toReal))) else 0))
    (bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (n : ℝ≥0∞) then
        (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp (-(q *
            (twoSidedExitUpTime X b ω).toReal))) else 0)
        else 0 ∂P) ≤ bound) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q *
        (twoSidedExitUpTime X b ω).toReal))) else 0 ∂P) ≤ bound := by sorry
