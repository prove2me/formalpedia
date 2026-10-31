-- Prove2me | Theorems.Thm_ForecastAggLearn_barL_gradient_convex
-- name    : ForecastAggLearn.barL_gradient_convex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:13.86851+00:00
-- url     : https://prove2.me/theorems/ef0c144d-436d-41b7-aca7-e04c304d216e
-- title:
--   §4.2.1 — gradient of $\overline L_t$, the bound $\|\nabla\overline L_t(h)\|\le\|\tilde z_t\|$, and convexity
-- statement:
--   Let $\tilde z\in\mathbb R^n$, $\tilde\mu\in\mathbb R$ and $\omega\in\{0,1\}$, and let $\overline L$ be the loss (4). For every $h\in\mathbb R^n$:
--
--   1. the gradient of $\overline L$ at $h$ is
--   $$
--   \nabla\overline L(h)=(1-\omega)\tilde z-\frac{\exp(-h\cdot\tilde z-\tilde\mu)}{1+\exp(-h\cdot\tilde z-\tilde\mu)}\,\tilde z ;
--   $$
--   2. $\|\nabla\overline L(h)\|\le\|\tilde z\|$;
--   3. the Hessian $\nabla^2\overline L(h)$ is positive semidefinite;
--   4. $\overline L$ is convex on $\mathbb R^n$.
--
--   These are the hypotheses of online gradient descent (Lemma 1): convex losses whose gradients are bounded by $Z\ge\|\tilde z_t\|$.
--
--   **Formalization Note** The Hessian is the second Fréchet derivative, and positive semidefiniteness is $D^2\overline L(h)(v,v)\ge0$ for all $v$.
--
--   Differences from the source:
--   - encoding: ∇²L̄_t(h) is positive semidefinite → fderiv ℝ (fderiv ℝ L̄) h v v ≥ 0 for all v; reason: the Hessian's quadratic form is the second Fréchet derivative on the diagonal
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, p.18

import Mathlib
import Definitions.Def_ForecastAggLearn_barL

namespace ForecastAggLearn

/-- **Gradient, gradient bound and convexity of `L̄_t`.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, p.18: "the gradient vector of L̄_t(h) is given by
∇L̄_t(h) = (1 − ω_t) z̃_t − exp(−h · z̃_t − µ̃_t)/(1 + exp(−h · z̃_t − µ̃_t)) z̃_t. Note also that for all
t ∈ [T], h ∈ ℝⁿ, since ω_t ∈ {0, 1}, we have that ‖∇L̄_t(h)‖ ≤ ‖z̃_t‖. Finally, [...] the Hessian
matrix of L̄_t(h), i.e., ∇²L̄_t(h), is positive semidefinite and hence, for all t ∈ [T], L̄_t(h) is
a convex function."

**Formalization Note.** On `EuclideanSpace ℝ (Fin n)`; `1 − ω_t` is `if ω then 0 else 1`. The
Hessian quadratic form is `v ↦ D²L̄_t(h)(v, v)`, the second Fréchet derivative. -/
theorem barL_gradient_convex {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (μt : ℝ) (ω : Bool) :
    (∀ h, HasGradientAt (barL z μt ω)
        ((if ω then (0 : ℝ) else 1) • z -
          (Real.exp (-(inner ℝ h z) - μt) / (1 + Real.exp (-(inner ℝ h z) - μt))) • z) h) ∧
      (∀ h, ‖(if ω then (0 : ℝ) else 1) • z -
          (Real.exp (-(inner ℝ h z) - μt) / (1 + Real.exp (-(inner ℝ h z) - μt))) • z‖ ≤ ‖z‖) ∧
      (∀ h v, 0 ≤ fderiv ℝ (fderiv ℝ (barL z μt ω)) h v v) ∧
      ConvexOn ℝ Set.univ (barL z μt ω) := by sorry

end ForecastAggLearn
