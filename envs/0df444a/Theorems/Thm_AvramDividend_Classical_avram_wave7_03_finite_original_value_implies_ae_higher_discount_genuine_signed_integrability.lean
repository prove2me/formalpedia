-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_implies_ae_higher_discount_genuine_signed_integrability
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_higher_discount_genuine_signed_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:02:44.97281+00:00
-- url     : https://prove2.me/theorems/55df4638-2091-48ef-aef5-275b15a3daed
-- title:
--   Finite actual original value supplies almost-everywhere genuine signed Stieltjes integrability at every stronger discount
-- statement:
--   If the genuine original-process dividendValue at discount q₁ is finite and q₂≥q₁, then for P-almost every original source sample path the real discounted Stieltjes integrand exp(-q₂*t) is IntegrableOn exactly paymentTimes(ruinTime X x D ω) against exactly dividendMeasure D ω. Use original value antitonicity, the accepted exact finite-value characterisation yielding almost-everywhere finite full ENNReal cash, and original pathwise iff for genuine signed integrability. Includes all original right-limit atom, continuous and jump cash; no surrogate stochastic process or measure.
-- source:
--   Proved source discount antitonicity a5978ae4; finite-value equivalence fd64314b; pathwise same-measure integrability iff a6d24d2f.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_higher_discount_genuine_signed_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hFinite : dividendValue X q₁ x D < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun t : ℝ => Real.exp (-(q₂ * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) := by sorry
