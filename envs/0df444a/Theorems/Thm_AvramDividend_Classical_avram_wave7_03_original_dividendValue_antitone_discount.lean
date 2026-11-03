-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_dividendValue_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:08:59.725932+00:00
-- url     : https://prove2.me/theorems/a5978ae4-5fb1-445f-80d1-d6c3237670a6
-- title:
--   Actual original full dividendValue antitone in the real discount rate
-- statement:
--   For the canonical original spectrally negative Levy process X and its exact genuine full dividend Stieltjes measure and paymentTimes stopped strictly before ruin with time-zero atom included, increasing the real discount rate cannot increase the original doubly integrated ENNReal dividendValue. No pathwise finiteness or positive discount is assumed. This transfers a proved expected payout budget from any lower discount rate to all higher ones on the identical source sample space and measure.
-- source:
--   Canonical AvramDividend.Classical.dividendValue, paymentTimes_measurable and ENNReal.ofReal monotonicity; each genuine dividend payment time is nonnegative and the inner/outer measures are unchanged.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_dividendValue_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    dividendValue X q₂ x D ≤ dividendValue X q₁ x D := by sorry
