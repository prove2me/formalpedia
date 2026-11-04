-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_p4f_expected_cash_antitone_discount
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_p4f_expected_cash_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:43:53.852669+00:00
-- url     : https://prove2.me/theorems/80e23094-3cb7-4980-8331-dc7da995beb2
-- title:
--   Expected source-exact ruin-stopped dividend Cash decreases with discount rate
-- statement:
--   For the same original dividend path, true ruin-stopped finite horizon and integrable P4-F-style real cash fields at two discount rates 0≤q1≤q2, the expected cash at the higher rate is at most expected cash at the lower rate. Source payment times are nonnegative, making the actual ENNReal cash antitone; source finite-horizon Cash finiteness permits the monotone conversion to real before ordinary integral monotonicity is applied. No density or atomlessness assumptions.
-- source:
--   Proved original stopped cash antitone discount and literal cash finiteness, Mathlib integral_mono

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_p4f_expected_cash_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash₁ Cash₂ : Ω → ℝ)
    (hCash₁ : ∀ ω, Cash₁ ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q₁ * s))) ∂(dividendMeasure D ω)).toReal)
    (hCash₂ : ∀ ω, Cash₂ ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q₂ * s))) ∂(dividendMeasure D ω)).toReal)
    (hI₁ : Integrable Cash₁ P) (hI₂ : Integrable Cash₂ P) :
    (∫ ω, Cash₂ ω ∂P) ≤ (∫ ω, Cash₁ ω ∂P) := by sorry
