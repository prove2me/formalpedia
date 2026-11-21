-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_future_negative_mark_indep_centered_integral_crosszero
-- name    : AvramDividend.Classical.avram_pj_original_future_negative_mark_indep_centered_integral_crosszero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:14:24.544628+00:00
-- url     : https://prove2.me/theorems/e8c8a5e9-fa9d-4ad4-9338-67c365c2e3b3
-- title:
--   Original future negative-mark centred count is orthogonal to independent past observables
-- statement:
--   An independent pair of integrable original random variables has the expected product equal to the product of expectations; a future compensated negative Levy mark increment of mean zero is therefore orthogonal to an integrable measurable past weight. This isolates the probability-theoretic step needed to certify original cross-grid moment cancellation.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_future_negative_mark_indep_centered_integral_crosszero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Past Future : Ω → ℝ)
    (hIndep : IndepFun Past Future P)
    (hPast : Integrable Past P)
    (hFuture : Integrable Future P)
    (hCentered : (∫ ω, Future ω ∂P) = 0) :
    (∫ ω, Past ω * Future ω ∂P) = 0 := by sorry
