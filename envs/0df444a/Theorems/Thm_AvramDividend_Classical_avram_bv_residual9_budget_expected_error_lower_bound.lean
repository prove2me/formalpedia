-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_budget_expected_error_lower_bound
-- name    : AvramDividend.Classical.avram_bv_residual9_budget_expected_error_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:45:53.466381+00:00
-- url     : https://prove2.me/theorems/67b98e7a-320f-41ae-91eb-9ad278033769
-- title:
--   A negative expected stopped-generator budget forces nonvanishing expected error
-- statement:
--   Generic probability-measure necessity: if a nonnegative integrable stopped payoff is bounded by initial value plus an integrable mean-zero correction, integrable B and integrable nonnegative error, while the expected B is below minus initial value minus a positive epsilon, the expected error is at least epsilon at every grid. This isolates an exact quantitative obstruction to source-exact vanishing error, without claiming an original Lévy countermodel exists.
-- source:
--   AVRAM BV-RESIDUAL9 positive-error obstruction to original arbitrary grids

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_budget_expected_error_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a ε : ℝ) (hε : 0 < ε)
    (F M B E : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P ∧ ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hE : ∀ n, Integrable (E n) P)
    (hBneg : ∀ n, (∫ ω, B n ω ∂P) ≤ -a - ε)
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + E n ω) :
    ∀ n, ε ≤ ∫ ω, E n ω ∂P := by sorry
