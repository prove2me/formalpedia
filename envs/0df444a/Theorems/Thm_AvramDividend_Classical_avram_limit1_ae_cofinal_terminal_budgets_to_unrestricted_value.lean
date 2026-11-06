-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
-- name    : AvramDividend.Classical.avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:44:52.133851+00:00
-- url     : https://prove2.me/theorems/bf3a10f1-12b0-4a23-9ea7-914c95e1528b
-- title:
--   Almost-sure cofinal original stopped terminal budgets control unrestricted perpetual dividend value
-- statement:
--   For the original spectrally negative Lévy model and unrestricted admissible dividend strategies, suppose every original admissible strategy D has measurable, pathwise increasing extended stopped clocks σ_k whose supremum is the actual ruinTime almost surely, plus nonnegative ENNReal terminal contributions whose sum with stopped genuine dividend-measure cash has expected budget B at every natural closed horizon and every clock. Then the unrestricted original dividend value function is ≤ B. Apply Proved a.s.-cofinal stopped Itô terminal Fatou bridge a8ff7bd6 at each closed horizon, Proved dividendValue_le_of_uniform_truncated_bounds dc933bd8 to each actual D, and two indexed supremum inequalities for valueFunction. Neither cofinality, measurability, stochastic Itô, integrability nor terminal vanishing is inferred; all appear as explicit source-bound hypotheses.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (B : ℝ≥0∞)
    (hBudget : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissible X x D →
      ∃ σ : ℕ → Ω → ℝ≥0∞,
        (∀ k : ℕ, Measurable (σ k)) ∧
        (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
        (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
        ∃ Terminal : ℕ → Ω → ℝ≥0∞,
          ∀ n k : ℕ,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) +
              Terminal k ω) ∂P) ≤ B) :
    valueFunction X q x ≤ B := by sorry
