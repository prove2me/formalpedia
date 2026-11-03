-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:55:24.529347+00:00
-- url     : https://prove2.me/theorems/f5df271c-22c8-4108-9200-106461261b0d
-- title:
--   Original finite-horizon stopped ruin cash budget from almost-sure exhaustion of monotone spatial-localisation cash
-- statement:
--   For the actual source spectrally negative Levy process, original dividend strategy and exact paymentTimes/ruinTime/dividendMeasure reward, any measurable increasing sequence of nonnegative local cash observables that covers full source discounted cash almost surely transfers its uniform expected ENNReal bound to the full finite-horizon ruin cash. This is the honest reserve-state boundary and spatial localisation limit assumption W7-18 must supply, including overshoot and creeping events. No uniform integrability is required because local cash is nonnegative. W7-05/06/07 may incorporate nonnegative terminal value by dropping it before invoking this lemma; no canonical hypothesis is changed.
-- source:
--   Mathlib lintegral_mono_ae and lintegral_iSup; exact original source paymentTimes, ruinTime and dividendMeasure. No abstract surrogate risk process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k : ℕ, Measurable (LocalCash k))
    (hLocalMon : ∀ ω : Ω, Monotone (fun k : ℕ => LocalCash k ω))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ⨆ k : ℕ, LocalCash k ω)
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ, (∫⁻ ω, LocalCash k ω ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by sorry
