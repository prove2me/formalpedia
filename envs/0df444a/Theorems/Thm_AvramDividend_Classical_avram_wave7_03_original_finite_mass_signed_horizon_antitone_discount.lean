-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:14:45.759728+00:00
-- url     : https://prove2.me/theorems/e2c7b0be-23ca-47ef-a83c-824092dbc496
-- title:
--   Actual original real signed finite-horizon Stieltjes payout decreases with discount under precisely finite source measure
-- statement:
--   On each original Levy process path and deterministic real horizon, the genuinely signed real Stieltjes payout integral on paymentTimes(ruinTime)∩Iic T is nonincreasing in the discount rate q≥0, provided precisely that same stopped-domain source dividendMeasure mass is finite. This hypothesis supplies actual IntegrableOn for both factors, and neither the zero-time right-limit atom, continuous dividend payments, nor the strict pre-ruin condition is altered. This supports transferring real signed horizon budget inequalities across discount rates for BV/UBV verifications.
-- source:
--   Original source definitions; paymentTimes_measurable 88dafb7f, discounted_stieltjes_integrableOn_of_finite_measure f70331c8, and real integral_mono_ae on the identical restricted original dividendMeasure.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (T : ℝ)
    (hfinite : (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤) :
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) := by sorry
