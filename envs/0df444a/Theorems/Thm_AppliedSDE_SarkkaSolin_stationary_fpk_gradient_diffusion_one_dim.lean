-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_fpk_gradient_diffusion_one_dim
-- name    : AppliedSDE.SarkkaSolin.stationary_fpk_gradient_diffusion_one_dim
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:44:34.00373+00:00
-- url     : https://prove2.me/theorems/e11e7791-6b3d-4f27-9080-c91d94edf452
-- title:
--   Stationary Fokker–Planck density for a one-dimensional gradient diffusion
-- statement:
--   Särkkä and Solin (2019), Theorem 5.6, displayed SDE (5.25) and density (5.26). For q>0 and a twice continuously differentiable potential v whose Boltzmann factor exp(-v/q) is integrable with positive finite normaliser Z, the probability density p(x)=Z^{-1} exp(-v(x)/q) is nonnegative, integrates to one, and satisfies the stationary one-dimensional forward equation for drift f(x)=-v'(x)/2 and diffusion variance q. This is a one-dimensional nontrivial specialisation of the book's multidimensional theorem, retained explicitly as such.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   p(x)=Z^{-1}e^{-v(x)/q},\quad -\partial_x\!\left(-\frac12 v'(x)p(x)\right)+\frac q2\partial_x^2p(x)=0
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.6, eqs (5.25)–(5.27), printed p. 64. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.stationary_fpk_gradient_diffusion_one_dim
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hInt : Integrable (fun x : ℝ => Real.exp (-(v x / q))))
    (hZ : 0 < ∫ x : ℝ, Real.exp (-(v x / q))) :
    let Z : ℝ := ∫ x : ℝ, Real.exp (-(v x / q))
    let p : ℝ → ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
    (∀ x : ℝ, 0 ≤ p x) ∧
    (∫ x : ℝ, p x = 1) ∧
    (∀ x : ℝ,
      deriv (fun y : ℝ => (-(1 : ℝ) / 2 * deriv v y) * p y) x =
        q / 2 * deriv (fun y : ℝ => deriv p y) x) := by
  sorry
