-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
-- name    : AvramDividend.Classical.avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:52:31.983233+00:00
-- url     : https://prove2.me/theorems/a6017cb3-2084-4e94-b8d7-588e85be0570
-- title:
--   A.s.-cofinal stopped dividend and terminal budgets give both capped and unrestricted local value bounds
-- statement:
--   For every capped admissible strategy at every permitted nonnegative reserve, assume measurable pathwise-increasing random stopped clocks cofinal almost surely in the genuine ruin time, and for each natural closed horizon assume an expected original Stieltjes dividend-measure cash plus nonnegative ENNReal terminal bound by ENNReal.ofReal (w x). The existing source-exact a.s.-cofinal stopped Fatou theorem and integer closed-horizon dividend value comparison yield the per-strategy perpetual bound, and the Proved local supremum reducer gives the capped valueFunctionLe and unrestricted valueFunction when C is top. No terminal vanishing, bounded variation, stochastic Itô, or integrability premise is inferred.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ σ : ℕ → Ω → ℝ≥0∞,
          (∀ k : ℕ, Measurable (σ k)) ∧
          (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
          (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
          ∃ Terminal : ℕ → Ω → ℝ≥0∞,
            ∀ n k : ℕ,
              (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)) +
                Terminal k ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
