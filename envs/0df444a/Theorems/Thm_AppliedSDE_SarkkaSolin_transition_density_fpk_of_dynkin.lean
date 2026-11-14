-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_transition_density_fpk_of_dynkin
-- name    : AppliedSDE.SarkkaSolin.transition_density_fpk_of_dynkin
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:51:58.659725+00:00
-- url     : https://prove2.me/theorems/1c90076d-c7cf-45ba-9055-0b4922829eb2
-- title:
--   State-dependent transition density satisfies the forward Kolmogorov equation
-- statement:
--   Särkkä and Solin (2019), Theorem 5.10 and the forward part of Theorem 5.4. Let p(s,y;t,x) be the transition density of a scalar Markov diffusion with smooth state-dependent drift b and variance a. Assume p is a nonnegative normalised density, C² in terminal state x, has continuous time derivative, satisfies differentiation under the integral for compactly supported test functions, and satisfies the Dynkin generator identity for the transition law. Then for every starting state y and starting time s, at every later time t and terminal state x, ∂_t p(s,y;t,x)=−∂_x(b(x)p)+(1/2)∂²_x(a(x)p). The Dynkin identity is a genuine stochastic generator prerequisite and is stated separately from the PDE conclusion; establishing it from the SDE is an earlier chapter obligation. This goal covers variable coefficients and arbitrary initial states, beyond the Gaussian constant-coefficient special cases.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \partial_t p(s,y;t,x)=-\partial_x\!\left(b(x)p\right)+\frac12\partial_x^2\!\left(a(x)p\right)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorems 5.4 and 5.10, equations (5.11), (5.43), printed pp. 61, 68. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.transition_density_fpk_of_dynkin
    (b a : ℝ → ℝ) (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hreg : ∀ (s y t : ℝ), s < t → ContDiff ℝ 2 (p s y t))
    (htime : ∀ (s y t : ℝ), s < t →
      Continuous (fun x : ℝ => deriv (fun τ : ℝ => p s y τ x) t))
    (hpos : ∀ (s y t x : ℝ), s < t → 0 ≤ p s y t x)
    (hnorm : ∀ (s y t : ℝ), s < t →
      ∫ x : ℝ, p s y t x = 1)
    (hderiv : ∀ (s y t : ℝ), s < t →
      ∀ (φ : ℝ → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        deriv (fun τ : ℝ => ∫ x : ℝ, φ x * p s y τ x) t =
          ∫ x : ℝ, φ x * deriv (fun τ : ℝ => p s y τ x) t)
    (hDynkin : ∀ (s y t : ℝ), s < t →
      ∀ (φ : ℝ → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        deriv (fun τ : ℝ => ∫ x : ℝ, φ x * p s y τ x) t =
          ∫ x : ℝ,
            (b x * deriv φ x +
              a x / 2 * deriv (fun z : ℝ => deriv φ z) x) *
              p s y t x) :
    ∀ (s y t x : ℝ), s < t →
      deriv (fun τ : ℝ => p s y τ x) t =
        -deriv (fun z : ℝ => b z * p s y t z) x +
          (1 / 2 : ℝ) *
            deriv (fun z : ℝ =>
              deriv (fun w : ℝ => a w * p s y t w) z) x := by
  sorry
