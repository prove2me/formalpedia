-- Prove2me | Theorems.Thm_DbarRegularity_cauchyRiemann_lp_plane
-- name    : DbarRegularity.cauchyRiemann_lp_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:54:35.738698+00:00
-- url     : https://prove2.me/theorems/07eb3a4c-0aa5-4f51-a48e-a20ee4b40e0e
-- title:
--   The L^p a priori estimate for the Cauchy–Riemann operator on the plane
-- statement:
--   For every $1<p<\infty$ there is a constant $A_p$ such that every complex-valued function $f$ of class $C^1$ with compact support in $\mathbb{R}^2$ satisfies
--   $$\Big\|\frac{\partial f}{\partial x_1}\Big\|_p+\Big\|\frac{\partial f}{\partial x_2}\Big\|_p\le A_p\Big\|\frac{\partial f}{\partial x_1}+i\frac{\partial f}{\partial x_2}\Big\|_p,$$
--   where $\|\cdot\|_p$ is the $L^p(\mathbb{R}^2)$ norm.
--
--   **Formalization Note** $\mathbb{R}^2$ is `EuclideanSpace ℝ (Fin 2)` and $\partial f/\partial x_j$ is `fderiv ℝ f x (EuclideanSpace.single j 1)`. `ContDiff ℝ 1 f` and `HasCompactSupport f` are the hypotheses. The exponent is `ENNReal.ofReal p` with $p>1$ real, and the constant `A : ℝ≥0` is chosen before $f$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter III, § 1.3, Proposition 4, p. 60

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter III, § 1.3, Proposition 4 (p. 60): for `1 < p < ∞` there is
`A_p` such that every complex-valued `f` of class `C¹` with compact support in `ℝ²` satisfies
`‖∂f/∂x₁‖_p + ‖∂f/∂x₂‖_p ≤ A_p ‖∂f/∂x₁ + i ∂f/∂x₂‖_p`. -/
theorem cauchyRiemann_lp_plane (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin 2) → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1) +
            Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
