-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_signed_L1
-- name    : AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:57:49.290023+00:00
-- url     : https://prove2.me/theorems/30b84fba-1d20-4f95-96d1-eb6be1dbe50a
-- title:
--   Uniform original deterministic signed dividend budgets imply P-integrability at any measurable finite random clock
-- statement:
--   At the unaltered original Lévy sample space, admissible strategy and source dividendMeasure, a uniform upper real budget for genuine signed Stieltjes discounted payouts at integer horizons n+1 implies Integrable under P of the full signed Stieltjes payout at any measurable finite NNReal random clock. The original deterministic-to-random ENNReal budget supplies actual expected cash finiteness, which triggers the already accepted signed Stieltjes L1 theorem. All right-limit time-zero and strictly pre-ruin dividend payments are retained.
-- source:
--   Original deterministic signed budgets imply random-clock ENNReal budget; original finite-clock signed Stieltjes L1 under finite ENNReal cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hDetBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
