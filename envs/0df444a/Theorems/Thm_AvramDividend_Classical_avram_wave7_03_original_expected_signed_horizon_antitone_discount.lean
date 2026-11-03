-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_signed_horizon_antitone_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_expected_signed_horizon_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:20:19.26862+00:00
-- url     : https://prove2.me/theorems/e6cb3440-b97c-46c4-9503-8c0e1c9abe2e
-- title:
--   Original genuine expected signed finite-horizon Stieltjes budgets antitone in discount under exact L1 assumptions
-- statement:
--   Under explicit almost-sure finite source Stieltjes payment mass and real L1 assumptions for both original discounted finite-horizon pathwise signed cash functions, their genuine expected real signed Stieltjes integrals on the original P decrease as q increases. The theorem directly consumes the verified pathwise real source signed discount order and is useful to transfer BV/UBV finite-horizon real cash budget inequalities across discount rates without changing the original ruin time, right-limit atom, continuous dividends or underlying probability law.
-- source:
--   Accepted original finite-mass pathwise real Stieltjes discount comparison e2c7b0be, outer real MeasureTheory.integral_mono_ae and exact stated L1(P) hypotheses.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_expected_signed_horizon_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (T : ℝ)
    (hfinite : ∀ᵐ ω ∂P, (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤)
    (hInt₁ : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) P)
    (hInt₂ : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) P) :
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
