-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_gradient_fpk_multivariate
-- name    : AppliedSDE.SarkkaSolin.stationary_gradient_fpk_multivariate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:51:45.672964+00:00
-- url     : https://prove2.me/theorems/550074ea-48b7-42c5-8b15-716482118980
-- title:
--   Multidimensional gradient-diffusion stationary Fokker–Planck density
-- statement:
--   Särkkä and Solin (2019), Theorem 5.6, equations (5.25)–(5.27). Let n be any finite state dimension, including n=0, let q>0 and v be a C² potential on ℝⁿ. Assume exp(−v/q) is integrable and has a strictly positive normaliser Z. The density p(x)=Z⁻¹exp(−v(x)/q) is nonnegative and integrates to one. It solves the stationary Fokker–Planck equation for drift f=−(1/2)∇v and diffusion covariance qI, expressed as equality of the finite-coordinate divergences Σ_i ∂_i(f_i p)=(q/2)Σ_i ∂_i²p. This generalises the earlier one-dimensional draft to the textbook's finite-dimensional gradient diffusion with authentic coordinate derivatives.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   p(x)=Z^{-1}e^{-v(x)/q},\quad\nabla\cdot\!\left(-\frac12p\nabla v\right)=\frac q2\Delta p
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.6, Equations (5.25)–(5.27), printed p. 64. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators Topology

theorem AppliedSDE.SarkkaSolin.stationary_gradient_fpk_multivariate
    (n : ℕ) (q : ℝ) (hq : 0 < q)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (hInt : Integrable (fun x : Fin n → ℝ =>
      Real.exp (-(v x / q))))
    (hZ : 0 < ∫ x : Fin n → ℝ, Real.exp (-(v x / q))) :
    let Z : ℝ := ∫ x : Fin n → ℝ, Real.exp (-(v x / q))
    let p : (Fin n → ℝ) → ℝ := fun x =>
      Z⁻¹ * Real.exp (-(v x / q))
    (∀ x : Fin n → ℝ, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ x : Fin n → ℝ,
      (∑ i : Fin n,
        fderiv ℝ (fun y : Fin n → ℝ =>
          (-(1 / 2 : ℝ) *
            fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) x
          (Pi.single i (1 : ℝ))) =
      q / 2 * ∑ i : Fin n,
        fderiv ℝ (fun y : Fin n → ℝ =>
          fderiv ℝ p y (Pi.single i (1 : ℝ))) x
          (Pi.single i (1 : ℝ))) := by
  sorry
