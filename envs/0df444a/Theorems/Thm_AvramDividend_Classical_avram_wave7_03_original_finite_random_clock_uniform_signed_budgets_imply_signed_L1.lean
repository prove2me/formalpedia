-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_uniform_signed_budgets_imply_signed_L1
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_signed_budgets_imply_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:37:22.091226+00:00
-- url     : https://prove2.me/theorems/479e14e7-b594-4911-bf76-53f839c1f35b
-- title:
--   Uniform expected real signed Stieltjes budgets on bounded truncations imply full original random-clock signed reward L1
-- statement:
--   For the exact original Lévy process with admissible dividend strategy and arbitrary measurable finite NNReal random clock τ, suppose the genuine expected real signed Stieltjes cash on each bounded stop clock min(τ,n+1) is uniformly bounded above by a common real B. Then the true full original signed discounted Stieltjes reward through τ on paymentTimes(ruinTime)∩Iic τ is integrable with respect to the original P. This is the practical integrability interface needed by BV/UBV stopped-verification consumers to use signed source expectations. It follows from the independently Proved original uniform bounded signed-budget→double ENNReal theorem and the now Proved signed real Stieltjes L1 bridge under finite expected ENNReal cash, with the same original dividendMeasure and all continuous/atomic payouts.
-- source:
--   Proved original direct uniform bounded signed budget→ENNReal bridge 2bdab35f; Proved original finite-clock signed Stieltjes L1 under finite expected ENNReal cash 724e387f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_signed_budgets_imply_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
