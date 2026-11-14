-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_generator_formal_adjoint_one_dim
-- name    : AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_one_dim
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:50:02.292756+00:00
-- url     : https://prove2.me/theorems/58d33226-7e65-415f-bf58-71b16064bec0
-- title:
--   Generator and Fokker–Planck formal adjoint coincide against compactly supported tests
-- statement:
--   A mathematically rigorous one-dimensional distributional bridge for Särkkä and Solin (2019), Section 5.3, equations (5.10)–(5.12) and (5.36). For a twice continuously differentiable drift f, nonnegative diffusion-variance coefficient a, twice differentiable density p, and a twice continuously differentiable compactly supported test function φ, the integral of φ against the formal Fokker–Planck adjoint −(fp)′+(ap)″/2 equals the integral of p against the diffusion generator fφ′+aφ″/2. This is the nonconstant-coefficient analytical identity required to derive the weak FPK equation from Dynkin's formula. It makes no claim yet about existence of a diffusion density or distributional time differentiability.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \int\varphi\left(-(bp)'+\frac12(ap)''\right)\mathrm dx=\int p\left(b\varphi'+\frac a2\varphi''\right)\mathrm dx
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Chapter 5, equations (5.10)–(5.12), (5.36), printed pp. 60–64. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_one_dim
    (f a p φ : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (ha : ContDiff ℝ 2 a)
    (hp : ContDiff ℝ 2 p) (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ)
    (ha_nonneg : ∀ x : ℝ, 0 ≤ a x) :
    (∫ x : ℝ, φ x *
      (-deriv (fun y : ℝ => f y * p y) x +
        (1 / 2 : ℝ) *
          deriv (fun y : ℝ => deriv (fun z : ℝ => a z * p z) y) x)) =
    ∫ x : ℝ,
      (f x * deriv φ x +
        a x / 2 * deriv (fun y : ℝ => deriv φ y) x) * p x := by
  sorry
