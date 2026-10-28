-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_past_weighted_count_compensation_ws01b
-- name    : AvramDividend.Classical.poisson_past_weighted_count_compensation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:14:30.923878+00:00
-- url     : https://prove2.me/theorems/ab1ee335-e5b6-47c9-b0b0-f9b916135bc9
-- title:
--   Predictable one-step Poisson count compensation against an independent integrable past observable
-- statement:
--   For an actual probability space, any integrable measurable past observable H independent of a future Poisson count K of rate r satisfies E[H·K]=r E[H]. This is a genuine one-step stochastic compensation identity with independence of past and future, not an analytic generator identity.
-- source:
--   From Mathlib IndepFun integral factorisation and the canonically Proved public HasLaw Poisson mean. Building block for predictable simple jump-measure compensation before approximation to general stopped kernels.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_hasLaw_expected_count_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.poisson_past_weighted_count_compensation_ws01b
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → ℝ) (hHm : Measurable H) (hHi : Integrable H μ)
    (K : Ω → ℕ) (hKm : Measurable K)
    (hIndep : IndepFun H K μ)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) μ) :
    (∫ ω, H ω * (K ω : ℝ) ∂μ) =
      (∫ ω, H ω ∂μ) * (r : ℝ) := by sorry
