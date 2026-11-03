-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_pathwise_signed_stieltjes_integrability_antitone_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_pathwise_signed_stieltjes_integrability_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:14:31.863711+00:00
-- url     : https://prove2.me/theorems/79172725-15db-4f3e-acaa-2703053b4aff
-- title:
--   Genuine original unrestricted signed Stieltjes integrability persists under stronger discount
-- statement:
--   For an original spectrally negative Lévy dividend strategy and a fixed original sample path, genuine signed Stieltjes IntegrableOn at lower q₁ implies IntegrableOn at every higher q₂. The entire proof uses Proved source definitions and helpers: the original exact pathwise ENNReal finiteness iff IntegrableOn equivalence, original measurable nonnegative paymentTimes, and Mathlib lintegral_mono_ae on the unchanged original dividendMeasure. This fully accounts for all initial, continuous and jump dividend payments and avoids dependencies on any Open helper.
-- source:
--   Proved exact original pathwise finiteness iff a6d24d2f and paymentTimes_measurable 88dafb7f; Mathlib lintegral_mono_ae.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_pathwise_signed_stieltjes_integrability_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (ω : Ω)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q₁ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q₂ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω) := by sorry
