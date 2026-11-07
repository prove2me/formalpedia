-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
-- name    : AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:25:15.131859+00:00
-- url     : https://prove2.me/theorems/32674501-a0c8-4a9e-903e-73871e8bbc7b
-- title:
--   Two vanishing original BV positive source errors yield tight positive deficit convergence without signed B L1
-- statement:
--   For an actual stopped-grid payoff with two positive error budgets and potentially nonintegrable signed HJB source B, the exact positive payoff deficit is integrable and its mean tends to zero whenever both source-error means tend to zero. A common measurable deficit is required; neither F nor B needs to be integrable separately. This bridges physical contact/C1 errors to the original strict source Fatou witness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F M B ErrCell ErrContact : ℕ → Ω → ℝ) (base : ℝ)
    (hCell : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContact : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hExcessMeas : ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - (base + (M n ω + B n ω))) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCellZero : Tendsto
      (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactZero : Tendsto
      (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ n, Integrable
      (fun ω => max (F n ω - (base + (M n ω + B n ω))) 0) P) ∧
    Tendsto (fun n =>
      ∫ ω, max (F n ω - (base + (M n ω + B n ω))) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
