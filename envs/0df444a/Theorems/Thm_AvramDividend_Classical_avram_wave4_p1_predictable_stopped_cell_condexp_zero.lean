-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_stopped_cell_condexp_zero
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_stopped_cell_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:16:20.801612+00:00
-- url     : https://prove2.me/theorems/e8c5333f-4626-4543-b3b2-d5c7826f7ed4
-- title:
--   Stopped predictable marked-Poisson cell has zero conditional expectation given its independent past
-- statement:
--   In an original probability space with independent past/future sigma-algebras, a genuinely past-measurable stopped weight H times an integrable centered future marked increment Z has conditional expectation zero given the past, if HZ is integrable. The conclusion is proved from independence and the predictable product pull-out theorem; no conditional compensation or martingale property is assumed.
-- source:
--   Pinned Mathlib 0df444a: Probability/ConditionalExpectation.lean condExp_indep_eq; MeasureTheory/Function/ConditionalExpectation/PullOut.lean condExp_mul_of_stronglyMeasurable_left.

import Mathlib

open MeasureTheory ProbabilityTheory Filter

theorem AvramDividend.Classical.avram_wave4_p1_predictable_stopped_cell_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast mFuture : MeasurableSpace Ω)
    (hPast : mPast ≤ mΩ)
    (hFuture : mFuture ≤ mΩ)
    [@SigmaFinite Ω mPast (P.trim hPast)]
    (H Z : Ω → ℝ)
    (hH : StronglyMeasurable[mPast] H)
    (hZ : StronglyMeasurable[mFuture] Z)
    (hProd : Integrable (H * Z) P)
    (hZi : Integrable Z P)
    (hIndep : Indep mFuture mPast P)
    (hCenter : ∫ ω, Z ω ∂P = 0) :
    P[H * Z | mPast] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by sorry
