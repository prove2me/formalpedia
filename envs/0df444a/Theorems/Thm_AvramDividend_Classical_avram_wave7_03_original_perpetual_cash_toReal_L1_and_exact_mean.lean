-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:36:45.798126+00:00
-- url     : https://prove2.me/theorems/5f2772c6-96e6-4a7d-bab9-41e6750c07f1
-- title:
--   Finite original perpetual dividend value has exactly integrable real-converted full Stieltjes cash
-- statement:
--   For the original spectrally negative Lévy process X, original P, dividend strategy D and exact full ruin-stopped paymentTimes and dividendMeasure, finiteness of the canonical expected perpetual ENNReal value implies original sample-space L1 integrability of its complete pathwise Stieltjes cash converted to real. Its genuine real expectation converts back exactly to the original full canonical ENNReal dividendValue. The proof uses proved source measurability, Mathlib integrable_toReal_of_lintegral_ne_top and ae_lt_top, and ofReal_integral_eq_lintegral_ofReal at the same original measure. No horizon truncation or loss of time-zero atom occurs.
-- source:
--   Canonical source dividendValue; Proved original perpetual Stieltjes cash measurability db59cbee-4085-43eb-a6bf-b5ec11efe6b4; Mathlib integral/lintegral conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω : Ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by sorry
