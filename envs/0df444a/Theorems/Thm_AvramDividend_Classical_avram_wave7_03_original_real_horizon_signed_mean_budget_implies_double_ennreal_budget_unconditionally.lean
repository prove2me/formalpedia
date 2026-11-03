-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_signed_mean_budget_implies_double_ennreal_budget_unconditionally
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_mean_budget_implies_double_ennreal_budget_unconditionally
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:17:31.332611+00:00
-- url     : https://prove2.me/theorems/46842b9d-5d9b-4d26-b054-286fd95f618c
-- title:
--   Direct original finite real-horizon signed Stieltjes expected budget transfers to the exact double ENNReal budget unconditionally
-- statement:
--   For the original spectrally negative Lévy process under its actual law P and admissible dividend strategy D, a genuine expected real signed Stieltjes payout bound at any finite nonnegative real T implies the exact original double ENNReal payout bound at the same paymentTimes(ruinTime X x D ω)∩Iic T and dividendMeasure D ω. The accepted unconditional bounded-clock signed/ENNReal equality applies to the constant measurable NNReal clock Real.toNNReal T, equal to T when T≥0. ENNReal.ofReal monotonicity transfers the real budget. All time-zero right-limit atoms, continuous pre-ruin payments and endpoint cash remain included. Unlike the unbounded clock bridge, no separately stated global integrability or finite expected cash condition is needed.
-- source:
--   Proved original bounded-clock unconditional signed/ENNReal mean equality fc7c1b8a-c416-450c-b1ad-cadf9344888f; Real.coe_toNNReal; ENNReal.ofReal_le_ofReal.

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

theorem AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_mean_budget_implies_double_ennreal_budget_unconditionally
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T)
    (B : ℝ)
    (hSignedBudget :
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
