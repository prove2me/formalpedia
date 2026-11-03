-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:34:20.800876+00:00
-- url     : https://prove2.me/theorems/30a156e4-849f-4a3d-9f41-43cbc96f7e0c
-- title:
--   Nonnegativity of original random-clock full signed Stieltjes expected dividends
-- statement:
--   Under the original Levy process and cap-admissible dividend strategy, expected real discounted Stieltjes payments on the exact paymentTimes(ruinTime)∩Iic(τ ω) against original dividendMeasure D ω are nonnegative for every bounded measurable random clock τ. Proof is integral_nonneg twice from strict exponential positivity; the original time-zero right-limit atom, jumps, diffuse payments and strict ruin exclusion remain. Combined with accepted random clock L1 this provides a genuine sign premise for ENNReal.ofReal_toReal conversions.
-- source:
--   Real.exp_pos and Mathlib integral_nonneg at the original Stieltjes and probability measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    0 ≤ (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
