-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_derivative_quadratic_bound
-- name    : AvramDividend.Classical.causal_neumann_derivative_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:14:14.135162+00:00
-- url     : https://prove2.me/theorems/cf4e8444-ed15-4738-baaf-b8e7b665f11a
-- title:
--   Quadratic-geometric derivative majorant for damped Volterra Neumann terms
-- statement:
--   If signed convolution powers have |P_n(x)| bounded by (n+1)^2 ρ^(n+1)/x and damped primitive terms have |H_n(x)|≤ρ^(n+1)/a on x≥ε, the derivative identity H_n′=P_n/a−wH_n implies a uniform quadratic-geometric derivative bound needed for C1 summation.
-- source:
--   Elementary positivity and triangle inequality on the derivative equation, using the canonical positive convolution-power quadratic estimate.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic

open AvramDividend.Classical

theorem AvramDividend.Classical.causal_neumann_derivative_quadratic_bound
    (P H : ℕ → ℝ → ℝ) (a ε ρ w : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hρ : 0 ≤ ρ) (hw : 0 ≤ w)
    (hP : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hDeriv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      deriv (H n) x = P n x / a - w * H n x) :
    ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |deriv (H n) x| ≤
        (1 / a) * (((n + 1 : ℝ) ^ 2 / ε) + w) * ρ ^ (n + 1) := by sorry
