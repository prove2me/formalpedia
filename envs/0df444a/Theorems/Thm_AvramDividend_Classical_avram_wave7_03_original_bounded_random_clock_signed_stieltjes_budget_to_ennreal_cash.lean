-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:25:03.249516+00:00
-- url     : https://prove2.me/theorems/05b187e8-280b-4c21-b3a1-64af2935dad6
-- title:
--   Exact original bounded random-clock signed Stieltjes budget to stopped ENNReal payout bridge
-- statement:
--   For the canonical spectrally negative Levy X, probability P, admissible original dividend strategy D and its exact rightLimit Stieltjes measure, a genuine real signed expected discounted Stieltjes cash bound at an arbitrary bounded measurable random clock τ gives the exact double ENNReal cash bound on paymentTimes(ruinTime X x D ω) ∩ Iic (τ ω). No strict pre-ruin hypothesis on τ is needed: positive ruin-time boundary cash is still excluded by paymentTimes, and the time-zero atom remains. Original full process, all interior continuous/jump dividends and sample space are unchanged.
-- source:
--   Proved exact all-variation bounded random-clock original full ruin expected signed/ENNReal equality fc7c1b8a and Mathlib ENNReal.ofReal_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget :
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
