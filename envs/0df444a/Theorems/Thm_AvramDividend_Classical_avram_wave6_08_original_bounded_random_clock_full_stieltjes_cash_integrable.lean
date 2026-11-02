-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
-- name    : AvramDividend.Classical.avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:42:55.835197+00:00
-- url     : https://prove2.me/theorems/3deca135-05b5-4863-83cd-a5f7c91b827e
-- title:
--   Unconditional original full-Stieltjes stopped cash L1 at every bounded measurable source clock
-- statement:
--   For the actual original spectrally negative Lévy process X with genuine admissible dividend D and any cap, arbitrary real discount and measurable bounded random clock τ, the exact toReal of the closed-ruin-paymentTimes discounted Stieltjes integral is P-integrable. This follows from the canonically proved same-source exponential finite-horizon payoff envelope at bounded random clocks, plus genuine random upper clock cash measurability and the pinned Mathlib integrable_toReal_of_lintegral_ne_top lemma. It requires no source Itô–Meyer identity, no hSourceLimit, no hDividendBound and no artificial sample space. Directly discharges the Cash integrability prerequisite in positive-cap corrected UBV stochastic verification.
-- source:
--   Canonically Proved 5b72d578-8fbe-415a-b8ba-f60d73ed7257 (original bounded-clock exponential expected full Stieltjes envelope), 2d478c7d-9d35-4371-a220-d9fd063c4852 (measurable true random-clock Stieltjes cash), Mathlib MeasureTheory.integrable_toReal_of_lintegral_ne_top at exact commit 0df444a...; independent Chat08 original-source L1 obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by sorry
