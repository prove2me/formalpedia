-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
-- name    : AvramDividend.Classical.avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:23:59.581559+00:00
-- url     : https://prove2.me/theorems/2f3a059a-51b8-4395-85a3-6b3c8cebabca
-- title:
--   Original real perpetual Stieltjes payout is integrable and bounded by finite ENNReal value bound
-- statement:
--   The original IsDividendStrategy, ruinTime, paymentTimes and dividendMeasure remain unchanged. The finite ENNReal.ofReal B upper bound makes genuine perpetual dividendValue finite. The Proved original Wave 7 signed perpetual Stieltjes L1/outer-mean theorem establishes integrability of the exact full real discounted cash integral, including time-zero and all payment atoms, and identifies its ENNReal.ofReal mean with dividendValue. Pinned Mathlib ENNReal.ofReal_le_ofReal_iff, under 0 ≤ B, transfers the inequality to the real expected payout. No terminal vanishing, equality-in-law or alternate probability space is used. The bridge applies to BV and UBV value estimates without circular parent imports.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q B : ℝ)
    (hB : 0 ≤ B)
    (hValueBound : dividendValue X q x D ≤ ENNReal.ofReal B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
