-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_original_perpetual_signed_stieltjes_integrable_ae
-- name    : AvramDividend.Classical.avram_wave7_03_positive_discount_original_perpetual_signed_stieltjes_integrable_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:28:05.327408+00:00
-- url     : https://prove2.me/theorems/feca9cb4-f95e-47a3-b40b-64b2e02ef58a
-- title:
--   Every positive discount makes the unrestricted original real dividend Stieltjes integral genuinely integrable almost surely
-- statement:
--   For each original source admissible dividend process D and every strictly positive q, the genuine unrestricted discounted real Stieltjes cash on the actual ruin-stopped paymentTimes domain is well-defined as a real IntegrableOn integral for P-almost all original sample paths, and ENNReal.ofReal of that actual real integral equals its canonical source ENNReal fibre cash. No outer expected-cash finiteness or stronger q≥ψ(1) hypothesis is needed. The Proved original positive-discount almost-sure finite cash theorem gives the exact a.e. premise for the new same-domain pathwise integrability/equality bridge, so time-zero right payments, all continuous/diffuse and jump dividends, and strict pre-ruin conventions are preserved.
-- source:
--   Proved c3df986d-42ce-469d-99f0-41e67291a25c positive discount a.e finite original cash; new exact unrestricted pathwise original signed Stieltjes bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_positive_discount_original_perpetual_signed_stieltjes_integrable_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P,
      IntegrableOn
        (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω))
        (dividendMeasure D ω) ∧
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by sorry
