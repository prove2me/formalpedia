-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_strict_future_cash_antitone_random_lower_clocks
-- name    : AvramDividend.Classical.avram_wave7_03_original_expected_strict_future_cash_antitone_random_lower_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:55:10.995785+00:00
-- url     : https://prove2.me/theorems/4631c42a-7073-4fef-8c04-142132fba085
-- title:
--   Original expected strict future dividend Stieltjes cash is antitone in random lower clocks
-- statement:
--   On the original Ω and P, for any spectrally negative Lévy process X, any original dividend control D and any two real random lower clocks S≤T pathwise, the double ENNReal expected Stieltjes payout strictly after T is at most the same payout strictly after S. The precise paymentTimes(ruinTime) domain and dividendMeasure D ω remain unchanged. Strictly future Ioi clocks ensure that any rightpayment at the lower clock is excluded; all subsequent jump and continuous payout is counted.
-- source:
--   Pinned Mathlib lintegral_mono_set by Ioi interval inclusion and outer lintegral_mono on the canonical source P; no stochastic, integrability, measurable-clock or Open-theorem premises.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_expected_strict_future_cash_antitone_random_lower_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (S T : Ω → ℝ)
    (hST : ∀ ω, S ω ≤ T ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (S ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
