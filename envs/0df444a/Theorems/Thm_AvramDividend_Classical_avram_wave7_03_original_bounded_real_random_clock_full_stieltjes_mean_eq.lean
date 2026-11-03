-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:25:41.898971+00:00
-- url     : https://prove2.me/theorems/f1840802-b449-4c76-8afe-fc9f8a5f0e99
-- title:
--   Exact original real-valued bounded random-clock stopped Stieltjes expectation to ENNReal equality
-- statement:
--   Under the actual original spectrally negative Levy process and cap-admissible strategy, for any nonnegative measurable real-valued random clock τ bounded by a finite nonnegative NNReal T, the expected genuine discounted real Stieltjes payout on paymentTimes(ruinTime)∩Iic(τ ω) is exactly related by ENNReal.ofReal to the double ENNReal integral on the identical original domain, dividendMeasure and P. This retypes the already Proved NNReal random-clock theorem using τ.toNNReal and the exact real cast identity; all time-zero right-limit atoms, continuous cash and strict positive ruin exclusion remain.
-- source:
--   Proved original unconditional bounded random NNReal clock equality fc7c1b8a; Real.coe_toNNReal, exact_mod_cast and measurable function equality.

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

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ (T : ℝ))
    (hτMeas : Measurable τ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
