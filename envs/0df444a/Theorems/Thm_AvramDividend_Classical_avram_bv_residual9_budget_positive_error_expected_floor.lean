-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_budget_positive_error_expected_floor
-- name    : AvramDividend.Classical.avram_bv_residual9_budget_positive_error_expected_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:29:28.692837+00:00
-- url     : https://prove2.me/theorems/5ef8e568-cf46-48d0-afb3-6ec3d251a41a
-- title:
--   Centred cash-budget certificate forces the positive-error expectation to dominate the original signed residual deficit
-- statement:
--   Under a probability measure, if a nonnegative payoff is dominated by a constant plus a centred integrable martingale residual, an integrable signed drift budget and a nonnegative integrable error, then the mean positive error is at least minus the signed budget mean minus the constant. This is the exact expectation obstruction needed for an Avram physical-grid countermodel.
-- source:
--   AVRAM BV-RESIDUAL9 round-seven disproof support: expectation-of-budget contradiction; no assumptions on stochastic source of B.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_budget_positive_error_expected_floor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c : ℝ) (F M B Err : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hB : Integrable B P)
    (hErr : Integrable (fun ω => max (Err ω) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ c + M ω + B ω + max (Err ω) 0) :
    -(∫ ω, B ω ∂P) - c ≤
      (∫ ω, max (Err ω) 0 ∂P) := by sorry
