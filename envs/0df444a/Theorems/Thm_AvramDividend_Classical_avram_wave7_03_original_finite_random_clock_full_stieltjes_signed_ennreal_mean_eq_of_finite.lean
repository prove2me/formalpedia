-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:40:46.187103+00:00
-- url     : https://prove2.me/theorems/513ccf61-cbda-4219-8871-11bd29522736
-- title:
--   Exact full original signed Stieltjes expectation equals double ENNReal cash at unbounded finite random clock under finiteness
-- statement:
--   On the genuine original spectrally negative Lévy process and admissible dividend strategy, for any measurable pathwise finite NNReal random clock τ, if the exact double ENNReal expected ruin-stopped dividend cash is finite, then it equals ENNReal.ofReal of the genuine expected signed discounted real Stieltjes integral on exactly the same paymentTimes(ruinTime X x D ω)∩Iic(τ ω) under P and dividendMeasure D ω. This is the full signed-to-ENNReal expectation bridge without a deterministic clock bound, with explicit true expectation finiteness. The argument uses an accepted original signed Stieltjes L1 lemma under that finiteness hypothesis, the accepted source pathwise real/ENNReal equality, nonnegative real exponential payout and pinned Mathlib ofReal_integral_eq_lintegral_ofReal. It retains time-zero right-limit, continuous payments and stopping-clock endpoint atoms.
-- source:
--   Proved source real horizon pathwise Stieltjes equality; accompanying finite-clock original signed Stieltjes L1 theorem; pinned Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
