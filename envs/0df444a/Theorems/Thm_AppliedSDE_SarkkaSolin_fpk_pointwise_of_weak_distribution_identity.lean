-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_pointwise_of_weak_distribution_identity
-- name    : AppliedSDE.SarkkaSolin.fpk_pointwise_of_weak_distribution_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:51:32.162193+00:00
-- url     : https://prove2.me/theorems/21a60ae2-17a0-4336-a47e-a12c298bc1e0
-- title:
--   General-coefficient Fokker–Planck equation from its weak distributional identity
-- statement:
--   A rigorous analytical bridge towards Särkkä and Solin (2019), Theorem 5.4. Let a(x) be a smooth state-dependent diffusion variance, b(x) a smooth drift and ρ(t,x) a density twice continuously differentiable in x. Assume the time derivative exists with a continuous spatial version. If for every twice continuously differentiable compactly supported test function φ, the integral of φ against the Fokker–Planck residual ∂tρ+∂x(bρ)−(1/2)∂xx(aρ) vanishes at every t, then the residual vanishes pointwise. This is a nonconstant-coefficient weak-to-classical PDE theorem. Derivation of the weak identity directly from the SDE and an Itô/Dynkin formula is a separate essential obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \left(\forall\varphi\in C_c^2,\ \int\varphi(x)R(t,x)\,\mathrm dx=0\right)\Longrightarrow R(t,x)=0
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.4, equations (5.10)–(5.12), printed pp. 61–62, using the distributional fundamental lemma. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.fpk_pointwise_of_weak_distribution_identity
    (b a : ℝ → ℝ) (ρ : ℝ → ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hρ : ∀ t : ℝ, ContDiff ℝ 2 (ρ t))
    (hdtcont : ∀ t : ℝ,
      Continuous (fun x : ℝ => deriv (fun s : ℝ => ρ s x) t))
    (hweak : ∀ (t : ℝ) (φ : ℝ → ℝ),
      ContDiff ℝ 2 φ → HasCompactSupport φ →
        (∫ x : ℝ, φ x *
          (deriv (fun s : ℝ => ρ s x) t +
            deriv (fun y : ℝ => b y * ρ t y) x -
            (1 / 2 : ℝ) *
              deriv (fun y : ℝ =>
                deriv (fun z : ℝ => a z * ρ t z) y) x)) = 0) :
    ∀ (t x : ℝ),
      deriv (fun s : ℝ => ρ s x) t =
        -deriv (fun y : ℝ => b y * ρ t y) x +
          (1 / 2 : ℝ) *
            deriv (fun y : ℝ => deriv (fun z : ℝ => a z * ρ t z) y) x := by
  sorry
