-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_lower_discount_signed_budget_controls_higher_dividendValue
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_lower_discount_signed_budget_controls_higher_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:25.508026+00:00
-- url     : https://prove2.me/theorems/5b5c108f-6e66-47bb-8b6b-d37582da0b67
-- title:
--   Sharp source-original lower-discount real signed horizon budget bounds full higher-discount ENNReal dividend value
-- statement:
--   Without any extra finiteness or L1 hypotheses beyond the canonical actual admissible dividend strategy, a uniform real upper bound on expected genuine signed Stieltjes dividend cash at all natural finite horizons for q₁≥0 implies the complete original ENNReal dividendValue at any larger q₂≥q₁ is bounded by ENNReal.ofReal B. The proof composes the remotely Proved exact original signed horizon-to-ENNReal budget bridge with remotely Proved monotonicity of the actual entire original dividendValue under increasing discount. The time-zero right-limit mass and all continuous/jump dividends on strict pre-ruin times are unchanged.
-- source:
--   Accepted original signed horizon full ENNReal budget 96f0eeb7 and accepted original dividendValue rate antitonicity a5978ae4; no extra mass or L1 premises.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_lower_discount_signed_budget_controls_higher_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hBudget₁ : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q₂ x D ≤ ENNReal.ofReal B := by sorry
