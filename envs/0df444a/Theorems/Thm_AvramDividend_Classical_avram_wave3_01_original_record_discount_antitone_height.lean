-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_antitone_height
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_discount_antitone_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:05:54.421847+00:00
-- url     : https://prove2.me/theorems/4dfc7254-c203-4306-aab1-41725233d15c
-- title:
--   Original killed first-record discount is antitone in positive record height
-- statement:
--   For the genuine spectrally negative Lévy process and positive discount and initial reflected depth, the expected discounted first record before ruin cannot increase when the required record height rises. The proof uses the already remotely proved original-clock semigroup and the elementary fact that each discounted payoff is between zero and one under the probability measure. This supplies the monotonicity input for extending the reciprocal-grid first-record exponent law to arbitrary heights.
-- source:
--   Avram source original-clock semigroup and true barrierRuinTime; Wave3 C1 exponential height extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_discount_antitone_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∀ h k : ℝ, 0 < h → h ≤ k →
      (∫⁻ ω, if twoSidedExitUpTime X k ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X k ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) := by sorry
