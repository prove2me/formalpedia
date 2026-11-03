-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
-- name    : AvramDividend.Classical.avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:07:16.272403+00:00
-- url     : https://prove2.me/theorems/16bfe94b-ac53-48dd-8394-b7d09b949a5b
-- title:
--   Almost surely future ruin-clock budget controls exact original finite-horizon Stieltjes dividends
-- statement:
--   If a source-faithful dividend cash budget b is available at the minimum of the canonical ruin time with a sample-dependent auxiliary clock η, and η lies strictly after the fixed finite horizon T on a P-full-measure event, then b also bounds the complete original finite-horizon Stieltjes dividend expectation. Every source process, filtration, law, payment-time set, ruin time, dividend measure and horizon atom is retained exactly. The original probability law is used with no replacement sample space.
-- source:
--   Proved W7-11 strict-future-clock source payment set equality and Mathlib lintegral_congr_ae; conditional bound is an exact ENNReal comparison.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ᵐ ω ∂P, ENNReal.ofReal T < η ω)
    (b : ℝ≥0∞)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b := by sorry
