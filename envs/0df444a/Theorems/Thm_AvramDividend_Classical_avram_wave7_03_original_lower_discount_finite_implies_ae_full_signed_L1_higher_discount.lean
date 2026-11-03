-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_lower_discount_finite_implies_ae_full_signed_L1_higher_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_lower_discount_finite_implies_ae_full_signed_L1_higher_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:57:50.247522+00:00
-- url     : https://prove2.me/theorems/f5f4ad95-132d-47c0-8370-3af1bed5ce1a
-- title:
--   Finite expected genuine dividend payout at any lower discount rate gives almost-sure signed Stieltjes L1 at a higher rate
-- statement:
--   Given finite original discounted dividendValue at q0 and q0≤q, the actual signed real exponential payout factor at q is IntegrableOn the original strictly pre-ruin paymentTimes against the original dividendMeasure for P-almost every original sample path. Includes t=0 atom and all diffuse/jump payouts. Uses only existing Proved full source discount order and full payout finiteness equivalences.
-- source:
--   Proved dividendValue rate antitone a5978ae4, Proved finite iff a.e pathwise cash finite fd64314b, Proved pathwise cash finite iff signed L1 a6d24d2f.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_lower_discount_finite_implies_ae_full_signed_L1_higher_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₀ q : ℝ) (hq : q₀ ≤ q)
    (hFinite : dividendValue X q₀ x D < ⊤) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω) := by sorry
