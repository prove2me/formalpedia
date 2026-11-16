-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_nat_poisson_binomial_exp_tsum_20261115
-- name    : AvramDividend.Classical.avram_a25_nat_poisson_binomial_exp_tsum_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:31:12.333252+00:00
-- url     : https://prove2.me/theorems/6a87c7f6-d912-4397-99c4-b981af4eb008
-- title:
--   Natural binomial count exponential as a finite-support real tsum
-- statement:
--   For any natural k and real theta, the sum over all n of binomial(k,n)(exp theta-1)^n equals exp(theta*k). Although expressed as an infinite sum, it has support contained in 0..k. The finite binomial theorem and exp(θ)^k=exp(θk) give the result directly. This pure deterministic lemma supports a valid Tonelli proof of Poisson moment generating functions from count factorial moments.
-- source:
--   Finite binomial identity and Real.exp_nat_mul in pinned Mathlib.

import Mathlib
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a25_nat_poisson_binomial_exp_tsum_20261115 (k : ℕ) (θ : ℝ) :
    (∑' n : ℕ, (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n) =
      Real.exp (θ * (k : ℝ)) := by sorry
