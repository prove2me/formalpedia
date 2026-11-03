-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_all_strategies_lower_signed_budget_controls_higher_valueFunctionLe
-- name    : AvramDividend.Classical.avram_wave7_03_all_strategies_lower_signed_budget_controls_higher_valueFunctionLe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:41:59.518953+00:00
-- url     : https://prove2.me/theorems/e587ae12-aea5-43ca-b4de-439971f083d5
-- title:
--   Uniform lower-discount source signed Stieltjes budgets bound higher-discount capped optimal value
-- statement:
--   For the original spectrally negative Levy model, suppose the genuine finite-horizon expected real signed Stieltjes dividends at discount q₁≥0 are uniformly bounded by the same B for every capped admissible original strategy and positive integer horizon. Then for every q₂≥q₁ the exact original capped optimal valueFunctionLe X q₂ C x ≤ ENNReal.ofReal B. This uses two independently remotely Proved original-source theorems: capped valueFunctionLe antitone in discount and the uniform signed Stieltjes budget-to-capped optimal value at q₁. All Ω/P/ruinTime/right-limit/time-zero/continuous payments and IsAdmissibleLe source definitions are unchanged.
-- source:
--   Accepted capped valueFunctionLe discount antitonicity 4dac10f4 and accepted original all-admissible signed finite-horizon budget-to-valueFunctionLe 82c6abb7.

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_valueFunctionLe_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_all_strategies_lower_signed_budget_controls_higher_valueFunctionLe
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hBudget₁ : ∀ (D : ℝ≥0 → Ω → ℝ)
      (hD : IsAdmissibleLe X x C D) (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunctionLe X q₂ C x ≤ ENNReal.ofReal B := by sorry
