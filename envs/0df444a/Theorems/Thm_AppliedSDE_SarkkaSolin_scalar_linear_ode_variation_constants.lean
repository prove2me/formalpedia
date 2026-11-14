-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_scalar_linear_ode_variation_constants
-- name    : AppliedSDE.SarkkaSolin.scalar_linear_ode_variation_constants
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:53:04.860048+00:00
-- url     : https://prove2.me/theorems/d310bb16-a734-4a23-bbcf-4a82015e7113
-- title:
--   Variation-of-constants formula for an inhomogeneous scalar linear ODE
-- statement:
--   Särkkä and Solin (2019), Chapter 2.2–2.3, equations (2.31) and (2.36). Suppose b is continuous, x is differentiable on the nonnegative real line with initial state x0 and satisfies x′(t)=a x(t)+b(t) for a constant real drift coefficient a. Then every nonnegative-time solution has the explicit variation-of-constants representation exp(a t)x0+∫_0^t exp(a(t−s)) b(s)ds. This is the scalar source result and forms a reusable rigorous bridge to matrix-exponential linear state transition formulas later in the book. Unlike the already proved Picard–Lindelöf existence theorem, this identifies the actual solution.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   x(t)=e^{at}x_0+\int_0^t e^{a(t-s)}b(s)\,\mathrm ds
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Chapter 2, Sections 2.2–2.3, Equations (2.31) and (2.36), printed pp. 10–11. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.scalar_linear_ode_variation_constants
    (a x₀ : ℝ) (b x : ℝ → ℝ)
    (hb : Continuous b)
    (hxcont : Continuous x)
    (hxdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ x t)
    (hx0 : x 0 = x₀)
    (hode : ∀ t : ℝ, 0 ≤ t → deriv x t = a * x t + b t) :
    ∀ t : ℝ, 0 ≤ t →
      x t = Real.exp (a * t) * x₀ +
        ∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * b s := by
  sorry
