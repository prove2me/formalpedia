-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
-- name    : AvramDividend.Classical.avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:27:33.227874+00:00
-- url     : https://prove2.me/theorems/1f7b7526-4d60-400e-9621-efdbab0afcd7
-- title:
--   Uniformly negative signed physical-grid budget contradicts a centred witness with vanishing positive-error expectation
-- statement:
--   For a sequence of source-compatible cash budgets, if each nonnegative payoff is dominated by a constant, centred integrable martingale, integrable drift budget and positive error, and each signed budget has mean at most the negative of that constant by a fixed positive amount, then the expected positive error cannot tend to zero. This is the exact sequence-level contradiction component for a possible non-refining original-grid disproof.
-- source:
--   Original Avram BV-RESIDUAL9 disproof support; derives directly from the previously Proved positive-error expectation floor using order closedness of real convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_budget_positive_error_expected_floor
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε : ℝ) (hε : 0 < ε) (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hNeg : ∀ n, (∫ ω, B n ω ∂P) ≤ -c - ε) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
