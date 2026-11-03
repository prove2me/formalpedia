-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
-- name    : AvramDividend.Classical.avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:30:51.488946+00:00
-- url     : https://prove2.me/theorems/fd64314b-6abc-4073-981d-ce0373acb73b
-- title:
--   General q exact original dividendValue finiteness iff genuine signed unrestricted Stieltjes L1 and almost-sure finite source cash
-- statement:
--   At arbitrary real discount q, finite expected original ENNReal Stieltjes dividendValue is equivalent to L1(P) integrability of the genuine real unrestricted signed Stieltjes integral and to almost sure finiteness of original inner ENNReal cash. This is exact including q=0 where the separate a.e. finiteness condition must be retained. Proof uses Proved cash toReal iff and Proved finite-pathwise full signed Stieltjes equality to transfer L1. Original Ω, P, X, paymentTimes, ruinTime, dividendMeasure are preserved.
-- source:
--   Previously Proved general original cash finiteness criterion  and 329453c6 unrestricted pathwise signed bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      (∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) < ⊤) := by sorry
