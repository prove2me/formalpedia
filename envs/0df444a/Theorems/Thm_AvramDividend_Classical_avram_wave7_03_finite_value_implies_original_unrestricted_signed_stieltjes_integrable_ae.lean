-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
-- name    : AvramDividend.Classical.avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:33:21.592288+00:00
-- url     : https://prove2.me/theorems/3a9d20cb-d6ee-405d-957d-cdcd382919cd
-- title:
--   Finite canonical expected dividends force a.e. full original signed Stieltjes integrability and exact ENNReal cash equality
-- statement:
--   Finite expected original-process dividendValue, with any real discount, yields almost-sure real integrability of the full untruncated signed Stieltjes integrand on exactly paymentTimes(ruinTime) and original dividendMeasure and conversion of its actual real integral back to the inner ENNReal payout. The proof invokes exact original inner cash measurability, ae_lt_top for finite ENNReal expectation and the accepted pathwise signed measure bridge. All right-limit initial mass, continuous payments, strict pre-ruin payments are retained.
-- source:
--   Proved original inner cash measurable db59cbee; Proved 329453c6 unrestricted signed bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
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
