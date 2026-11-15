-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
-- name    : AvramDividend.Classical.avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:54:13.320537+00:00
-- url     : https://prove2.me/theorems/69fed976-1861-416d-8471-bdba71b8267f
-- title:
--   Finite causal marked-jump exponential equals finite product of marked Laplace factors
-- statement:
--   For any finite set of nonnegative physical jump times, the real exponential of the causal sum of marks equals the finite product of the individual mark exponentials, including the observation-time cutoff.
-- source:
--   Pinned Mathlib Finset.mul_sum and Real.exp_sum; deterministic finite activity marked-jump bridge.

import Mathlib
open Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
    (S : Finset ℝ≥0) (j : ℝ≥0 → ℝ)
    (t : ℝ≥0) (θ : ℝ) :
    Real.exp (θ * (∑ u ∈ S, if u ≤ t then j u else 0)) =
      ∏ u ∈ S, if u ≤ t then Real.exp (θ * j u) else 1 := by sorry
