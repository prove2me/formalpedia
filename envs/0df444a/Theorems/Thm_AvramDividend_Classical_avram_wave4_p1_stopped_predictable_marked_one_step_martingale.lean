-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_one_step_martingale
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_one_step_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:16:22.863769+00:00
-- url     : https://prove2.me/theorems/07dc3527-3a6d-4bf9-b8c5-bbb2f4676cd5
-- title:
--   Original-path stopped marked-Poisson predictable one-step martingale equality
-- statement:
--   For an original-process adapted integrable prefix G, a past-measurable stopped coefficient H, and a centered integrable future marked increment Z independent of the past sigma-algebra, prove E[G+HZ | past]=G. This supplies a genuine conditional one-step martingale interface from independence, integrability and adaptedness; no compensated martingale condition or Campbell conclusion is assumed.
-- source:
--   Pinned Mathlib 0df444a Probability.ConditionalExpectation condExp_indep_eq; ConditionalExpectation.PullOut condExp_mul_of_stronglyMeasurable_left; ConditionalExpectation.Basic condExp_add and condExp_of_stronglyMeasurable.

import Mathlib

open MeasureTheory ProbabilityTheory Filter

theorem AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_one_step_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast mFuture : MeasurableSpace Ω)
    (hPast : mPast ≤ mΩ)
    (hFuture : mFuture ≤ mΩ)
    [@SigmaFinite Ω mPast (P.trim hPast)]
    (G H Z : Ω → ℝ)
    (hG : StronglyMeasurable[mPast] G)
    (hGi : Integrable G P)
    (hH : StronglyMeasurable[mPast] H)
    (hZ : StronglyMeasurable[mFuture] Z)
    (hProd : Integrable (H * Z) P)
    (hZi : Integrable Z P)
    (hIndep : Indep mFuture mPast P)
    (hCenter : ∫ ω, Z ω ∂P = 0) :
    P[G + H * Z | mPast] =ᵐ[P] G := by sorry
