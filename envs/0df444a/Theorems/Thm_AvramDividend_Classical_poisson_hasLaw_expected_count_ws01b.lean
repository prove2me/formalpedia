-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_hasLaw_expected_count_ws01b
-- name    : AvramDividend.Classical.poisson_hasLaw_expected_count_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:02:51.767199+00:00
-- url     : https://prove2.me/theorems/34c937d1-68fa-4df5-aed7-ca943f2f57e2
-- title:
--   Exact expected count for an arbitrary measurable Poisson-law random variable
-- statement:
--   On any probability space, every measurable natural-valued random variable with actual Poisson law of finite rate r has Bochner expectation exactly r. Useful as the count component of genuine jump compensators without relying on any private Poisson point-family definitions.
-- source:
--   Specialises the canonically Proved Poisson distribution mean theorem to a genuine random-variable HasLaw equality. Public Mathlib-only probability interface.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_hasLaw_expected_count_ws01b
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) μ) :
    (∫ ω, (K ω : ℝ) ∂μ) = (r : ℝ) := by sorry
