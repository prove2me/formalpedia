-- Prove2me | Theorems.Thm_ConvexOptimization_convexOn_iff_hessian_nonneg
-- name    : ConvexOptimization.convexOn_iff_hessian_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:40:16.226567+00:00
-- url     : https://prove2.me/theorems/1e7766fc-1136-4651-bd3f-e489be181d66
-- title:
--   Second-order characterization of convexity
-- statement:
--   **Second-order characterization of convexity:** a twice differentiable function is convex exactly when its Hessian is positive semidefinite.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and convex and let $f$ be twice continuously differentiable on $\Omega$. Then
--
--   $$f \text{ is convex on } \Omega \qquad\Longleftrightarrow\qquad \langle \nabla^2 f(x)\, v,\, v\rangle \ge 0 \quad \text{for every } x \in \Omega \text{ and every } v \in \mathbb{R}^n,$$
--
--   i.e. $\nabla^2 f(x) \succeq 0$ throughout $\Omega$.
--
--   This is the criterion one actually applies to a concrete function: convexity of a quadratic form reduces to positive semidefiniteness of its matrix, and convexity along every line is exactly nonnegativity of the second derivative of the restriction. Strengthening the right-hand side to $\nabla^2 f(x) \succeq mI$ with $m > 0$ gives strong convexity, the hypothesis under which the convergence rates of later missions are stated.
--
--   **Formalization Note** Smoothness is `ContDiffOn ℝ 2 f Ω`, and the Hessian appears as the iterated Fréchet derivative `fderiv ℝ (fderiv ℝ f) x v v` rather than as a matrix, which avoids choosing a basis; openness of `Ω` is needed for these derivatives to be defined at every point of the domain. Source: B&V §3.1.4, p. 71.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 71, §3.1.4 (second-order conditions for convexity)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.convexOn_iff_hessian_nonneg {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 2 f Ω) :
    ConvexOn ℝ Ω f ↔
      ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  sorry
