-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_square_integral_upper_from_count_moment_budget_20261122
-- name    : AvramDividend.Classical.avram_oai_square_integral_upper_from_count_moment_budget_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:04:30.775813+00:00
-- url     : https://prove2.me/theorems/e91b564e-2927-4cac-b6a4-7086d78c8923
-- title:
--   Quantitative squared expectation majorant for a count-dominated centred signed random variable
-- statement:
--   A real centred stochastic residual J dominated almost surely by the nonnegative count N plus a deterministic compensator c satisfies E[J²] ≤ 2 R + 2 c² whenever E[N²] ≤ R. This mathematical statement transfers the original physical bounded negative mark count-square estimate into an explicit quantitative energy estimate for the original Lévy process. It is a deterministic probability-analytic inequality, not an assumed Poisson isometry.

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_square_integral_upper_from_count_moment_budget_20261122
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (c R : ℝ)
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (hN2 : Integrable (fun ω => (N ω) ^ 2) P)
    (hNBound : (∫ ω, (N ω) ^ 2 ∂P) ≤ R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hDom : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |c|) :
    (∫ ω, (J ω) ^ 2 ∂P) ≤ 2 * R + 2 * c ^ 2 := by sorry
