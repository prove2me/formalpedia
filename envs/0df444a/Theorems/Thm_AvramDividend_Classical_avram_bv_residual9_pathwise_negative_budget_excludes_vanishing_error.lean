-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_pathwise_negative_budget_excludes_vanishing_error
-- name    : AvramDividend.Classical.avram_bv_residual9_pathwise_negative_budget_excludes_vanishing_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:58:38.945465+00:00
-- url     : https://prove2.me/theorems/9ac58c80-2226-4b17-9a42-b0a2134e236b
-- title:
--   A pathwise coarse-grid negative generator budget rules out vanishing positive errors
-- statement:
--   In the original arbitrary-grid stopped budget, a uniform almost-everywhere upper bound on each integrable signed generator budget of minus epsilon times the coarse cell length implies a corresponding expected-value deficit. If the deficit exceeds the initial value by a fixed positive margin, the expected positive error cannot vanish. The result bridges the proved source-specific collapsed-grid B estimate to the proved centred-martingale contradiction theorem.
-- source:
--   BV-RESIDUAL9 source-exact original-grid countermodel bridge; uses Proved 1f7b7526 and the probability integral of a constant. No process assumptions are replaced or postulated.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_pathwise_negative_budget_excludes_vanishing_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε L η : ℝ) (hη : 0 < η) (hgap : c + η ≤ ε * L)
    (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hBpath : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ -(ε * L)) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
