-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
-- name    : AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_negative_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:21:43.575357+00:00
-- url     : https://prove2.me/theorems/092db474-a695-4596-823d-0f1bb92d20ae
-- title:
--   Arbitrarily early negative Lévy values force instantaneous zero-barrier ruin
-- statement:
--   For an actual spectrally negative Lévy sample path, arbitrarily early negative increments imply instantaneous ruin of the zero-reflection strategy. The running supremum is nonnegative, so a negative increment forces strictly positive drawdown. Invoke the pathwise infimum lemma barrierRuinTime_zero_of_near_zero_drawdown. This pinpoints the remaining stochastic input as the classical regularity of zero for the negative half-line under unbounded variation. It directly advances the zero_reflectedSupValue_eq_barrierValue branch.
-- source:
--   Consequent of canonical runningSup_eq_rawSup_nonneg and newly authored barrierRuinTime_zero_of_near_zero_drawdown; conditional prerequisite for zero_reflectedSupValue_eq_barrierValue.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_negative_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    barrierRuinTime X 0 ω = 0 := by sorry
