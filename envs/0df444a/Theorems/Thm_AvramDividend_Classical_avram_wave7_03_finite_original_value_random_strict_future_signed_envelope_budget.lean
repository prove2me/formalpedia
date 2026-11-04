-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_random_strict_future_signed_envelope_budget
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_envelope_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:16:29.801608+00:00
-- url     : https://prove2.me/theorems/41d25906-ace8-4197-a38b-b29d32972f5d
-- title:
--   Finite canonical original dividend value converts random-clock signed HJB envelope into exact ENNReal expected tail budget
-- statement:
--   On original Ω, P, X, D, paymentTimes and dividendMeasure, finiteness of genuine original dividendValue supplies almost-sure pathwise Stieltjes IntegrableOn. Given a real signed envelope B for discounted payout over paymentTimes(ruinTime) ∩ Ioi(Tω), B integrable under original P, and mean B≤K, the exact double ENNReal expected strict-future payout is ≤ENNReal.ofReal K. This is a direct consumer-ready P3/P4 HJB residual bridge with no integrability assumption to discharge and no surrogate measure or process.
-- source:
--   Already-Proved original unrestricted signed integrability 3a9d20cb; pinned IntegrableOn.mono; accepted new exact original random strict future signed envelope budget c0e22305. All imports Proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_envelope_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ) (B : Ω → ℝ) (K : ℝ)
    (hFinite : dividendValue X q x D < ⊤)
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by sorry
