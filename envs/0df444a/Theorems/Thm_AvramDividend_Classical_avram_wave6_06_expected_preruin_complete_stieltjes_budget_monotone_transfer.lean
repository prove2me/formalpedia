-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_expected_preruin_complete_stieltjes_budget_monotone_transfer
-- name    : AvramDividend.Classical.avram_wave6_06_expected_preruin_complete_stieltjes_budget_monotone_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:49:20.410954+00:00
-- url     : https://prove2.me/theorems/b6d5f8db-35c7-4f76-9210-e86600417ad3
-- title:
--   Actual expected pre-ruin complete Stieltjes cash inherits a uniform bounded-clock HJB budget by monotone convergence
-- statement:
--   For the true original spectrally negative Lévy process X, its original adapted dividend strategy D and original ruin time, take measurable increasing extended stopping clocks converging pathwise to ruin. If every clock-localised expected complete discounted pre-ruin Stieltjes reward is bounded by the same nonnegative HJB candidate initial value, then the true full pre-ruin expectation at any fixed finite time horizon is bounded by that value. Compose the already Proved exact expected random-clock Stieltjes monotone-localisation equality with iSup_le. Includes simultaneous/time-zero right dividend atoms and all continuous/singular/jump components; does not postulate source Itô–Meyer identity.
-- source:
--   Avram–Palmowski–Pistorius, Proposition 4(i), passage from (5.13) by monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_expected_preruin_complete_stieltjes_budget_monotone_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ) (w : ℝ → ℝ)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudget : ∀ n,
      (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
