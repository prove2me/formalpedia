-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_discount_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:19:44.406763+00:00
-- url     : https://prove2.me/theorems/7a08c9f8-d2f2-4c32-a54f-429d24f82029
-- title:
--   Original reflected-killed first-record discount is at most one
-- statement:
--   For the actual source spectrally negative Lévy probability measure, the discounted first-upcrossing reward before reflected ruin is pointwise at most one, so its extended nonnegative integral is at most the probability mass of the space. This proves the actual factor is finite, permitting sound conversion of the accepted ENNReal semigroup to a real multiplicative semigroup. There is no Standing or C1 hypothesis.
-- source:
--   Proved source probability X.isProbability and Mathlib lintegral_mono, Real.exp_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_discount_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) :
    ∀ a h : ℝ,
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ≤ 1 := by sorry
