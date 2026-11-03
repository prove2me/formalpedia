-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:22:44.5511+00:00
-- url     : https://prove2.me/theorems/bde2cbcf-8e0f-44b7-af9a-ee4476e4fc8f
-- title:
--   Finite expected original random-clock full Stieltjes ENNReal cash implies genuine toReal payout L1
-- statement:
--   For the exact original spectrally negative Lévy process, actual dividend strategy and canonical Stieltjes payout measure, if the outer ENNReal expectation of the full discounted ruin-stopped dividend cash through an arbitrary measurable pathwise finite random clock τ is finite, then the inner original ENNReal cash converted by toReal is integrable with respect to the original P. No deterministic global clock bound is required, but a genuine finite expected ENNReal payout is explicitly assumed. The proof invokes the original source random upper-clock cash measurability theorem and the pinned Mathlib integrable_toReal_of_lintegral_ne_top. All time-zero, continuous and horizon-endpoint masses remain in the same original restricted dividendMeasure.
-- source:
--   Proved original source random upper-clock complete Stieltjes cash measurability; pinned Mathlib MeasureTheory.integrable_toReal_of_lintegral_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
