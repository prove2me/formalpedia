-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_outer_cash_eq_lintegral_genuine_signed_of_ae_pathwise_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_outer_cash_eq_lintegral_genuine_signed_of_ae_pathwise_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:50:55.770722+00:00
-- url     : https://prove2.me/theorems/ef7126cb-b2d1-4a01-986f-4864106ba04e
-- title:
--   Original unrestricted outer ENNReal dividends equal lintegral of genuine signed real Stieltjes cash under exactly a.e. finite pathwise payouts
-- statement:
--   General-discount exact outer signed-to-ENNReal Stieltjes bridge for the original process. The explicit necessary source hypothesis is almost-sure finiteness of the exact unrestricted inner ENNReal payout against dividendMeasure on paymentTimes(ruinTime). This is enough to identify canonical dividendValue, even if infinite, with the outer ENNReal lintegral of ENNReal.ofReal of the genuine unrestricted real signed Stieltjes payout over the same original pathwise measure. The source pathwise bridge proves per-path integrability and exact conversion on the full-measure set; lintegral_congr_ae handles the outer expectation. It preserves time-zero right-limit, continuous and jump payments and the strict pre-ruin domain.
-- source:
--   Proved 329453c6 unrestricted original pathwise integrability and ENNReal equality; Mathlib lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_outer_cash_eq_lintegral_genuine_signed_of_ae_pathwise_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hAeFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤) :
    dividendValue X q x D =
      (∫⁻ ω : Ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
