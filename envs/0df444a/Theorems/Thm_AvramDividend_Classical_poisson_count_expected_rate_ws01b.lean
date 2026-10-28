-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
-- name    : AvramDividend.Classical.poisson_count_expected_rate_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:28:35.968654+00:00
-- url     : https://prove2.me/theorems/951829c1-447e-4e44-910f-e6c465dda134
-- title:
--   Exact Bochner mean of a Poisson jump count equals its finite rate
-- statement:
--   For every nonnegative finite Poisson intensity r, the actual Bochner expected natural-valued Poisson count equals r. A stochastic intensity input to Campbell's formula and compound-Poisson jump compensators.
-- source:
--   Adapted from LeanLevy/Probability/Poisson.lean, Poisson first moment, MIT licence (LeanLevy Contributors, 2026), using Mathlib poissonMeasure_real_singleton and hasSum_one_poissonMeasure at pinned revision. This theorem is not the predictable PRM compensator.

import Mathlib

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_count_expected_rate_ws01b (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)) = (r : ℝ) := by sorry
