-- Prove2me | Theorems.Thm_AvramDividend_Classical_stochastic_budget_finite_horizon_telescope
-- name    : AvramDividend.Classical.stochastic_budget_finite_horizon_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:44:07.917715+00:00
-- url     : https://prove2.me/theorems/93ee58b5-7b07-445e-b003-297b178b9d38
-- title:
--   Telescoping finite-horizon nonnegative discounted stochastic budgets
-- statement:
--   Suppose v(k) is the nonnegative discounted continuation value and r(k) is the nonnegative discounted reward for a discrete-time controlled reserve at stage k. If every one-step expected-value budget satisfies v(k+1)+r(k)≤v(k), then the reward accumulated through any finite horizon together with the terminal continuation value is at most the initial value. This algebraic bridge allows Proved Lévy one-step semigroup inequalities to be assembled into a global finite-grid verification estimate without losing the terminal residual.
-- source:
--   Elementary finite-horizon dynamic-programming telescope used in the discrete-time approximation of Proposition 4(i), Avram, Palmowski and Pistorius (2007).

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.stochastic_budget_finite_horizon_telescope
    (v r : ℕ → ℝ≥0∞)
    (hstep : ∀ k, v (k + 1) + r k ≤ v k)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, r k) + v n ≤ v 0 := by sorry
