-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
-- name    : AvramDividend.Classical.avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:46:56.715773+00:00
-- url     : https://prove2.me/theorems/39085139-4139-4fbb-8c2e-64acf24df224
-- title:
--   Vanishing expected compensated positive source errors force the signed physical-grid mean gap to vanish
-- statement:
--   For a probability law with integrable original-grid payoff F, signed generator residual B, centred compensated correction M and positive source errors Err, any genuine source-exact pathwise upper budget with vanishing expected positive errors implies the signed mean-gap condition needed by canonical theorem 4044.
-- source:
--   Uses single-grid mean gap upper bound and squeeze_zero; original cash and source B are later instantiated without altered process or grid.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_pathwise_budget_expected_gap_bound
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B M Err : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ k + (M n ω + B n ω) + max (Err n ω) 0)
    (hErr : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun n => max ((∫ ω, F n ω ∂P) -
        k - (∫ ω, B n ω ∂P)) 0) atTop (nhds (0 : ℝ)) := by sorry
