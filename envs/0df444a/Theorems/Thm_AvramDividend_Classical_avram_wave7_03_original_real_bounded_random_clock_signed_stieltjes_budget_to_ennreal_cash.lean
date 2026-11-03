-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:38:43.734653+00:00
-- url     : https://prove2.me/theorems/32f667a2-0794-4ad6-aa6d-4e6c4d2dd2ac
-- title:
--   Original real-bounded real random-clock signed Stieltjes budget gives exact ENNReal cash budget
-- statement:
--   With the deterministic finite horizon T, nonnegative random clock τ and budget B all typed real, a bound on the genuine original expected real discounted Stieltjes payout on paymentTimes(ruinTime)∩Iic(τ ω) yields the corresponding double ENNReal payout bound on exactly the same domain and dividendMeasure under original P. Use the Proved original real/real random-clock Stieltjes expectation bridge 49da37f3 and ENNReal.ofReal monotonicity. Explicit hτMeas, hτNonneg and hτBound make the comparison genuine at the random stopped original process, including time-zero right-limit and diffuse payments.
-- source:
--   Proved W7-03 original real-bounded real-clock exact Stieltjes/ENNReal expectation identity 49da37f3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable τ) (B : ℝ)
    (hBudget :
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
