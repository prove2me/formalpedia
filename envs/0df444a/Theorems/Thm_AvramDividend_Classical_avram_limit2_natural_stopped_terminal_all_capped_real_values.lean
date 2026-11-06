-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_natural_stopped_terminal_all_capped_real_values
-- name    : AvramDividend.Classical.avram_limit2_natural_stopped_terminal_all_capped_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:59:25.074363+00:00
-- url     : https://prove2.me/theorems/1195ed30-3e33-44b8-9a0f-d287cfeaf69f
-- title:
--   Natural stopped terminal budgets give genuine all-capped-strategy real L1 and top-cap variational upper bounds
-- statement:
--   A genuine uniform original natural ruin-truncated cash-plus-terminal bound over every admissible strategy yields integrable real ruin-stopped Stieltjes payout and a real expected cash upper bound for every capped policy, a simultaneous cap-constrained valueFunctionLe bound, and at C=top the unrestricted original valueFunction bound. The original indexed suprema, time-zero and terminal payment atoms, and nonnegative terminal terms are unchanged. Uses already Proved natural-to-perpetual payout budget, real Stieltjes L1 transfer, and top-cap valueFunction identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_natural_stopped_terminal_all_capped_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hBudget : ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in
            paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P)
          ≤ ENNReal.ofReal (w x)) :
    (∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ (x : ℝ), 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
