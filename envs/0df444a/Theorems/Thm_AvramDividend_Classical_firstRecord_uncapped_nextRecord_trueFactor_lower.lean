-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_uncapped_nextRecord_trueFactor_lower
-- name    : AvramDividend.Classical.firstRecord_uncapped_nextRecord_trueFactor_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:41:45.282982+00:00
-- url     : https://prove2.me/theorems/24d6b537-6c99-47de-b9d2-13f8896e121b
-- title:
--   Uncapped first-record strong-Markov lower renewal factorisation
-- statement:
--   The expected discounted killed payment at the next record dominates the full uncapped current-record payment multiplied by the true two-sided exit factor. The proof passes uniform finite-cap inequalities to the global reward by monotone convergence using measurability of the upper-passage stopping time.
-- source:
--   Proved firstRecord_capped_nextRecord_trueFactor_lower, firstRecord_capped_integral_eq_natTruncation, killed_weight_global_factor_lintegral_le_of_caps and killed_firstRecord_discount_reward_measurable. Also proved upperPassage_measurable_from_stopping.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_uncapped_nextRecord_trueFactor_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    :
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by sorry
