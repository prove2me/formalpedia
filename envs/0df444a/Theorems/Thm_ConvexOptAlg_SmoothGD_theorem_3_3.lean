-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_theorem_3_3
-- name    : ConvexOptAlg.SmoothGD.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:06:05.259982+00:00
-- url     : https://prove2.me/theorems/9eecef85-86d6-4534-b947-6d489785639a
-- title:
--   Theorem 3.3, p. 267 — gradient descent with η = 1/β on a convex β-smooth f satisfies f(x_t) − f(x*) ≤ 2β‖x₁ − x*‖²/(t − 1)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, and let $x^*$ be a minimizer of $f$ on $\mathbb R^n$. Let $(x_t)_{t\ge1}$ be gradient descent with step size $\eta=1/\beta$ started at $x_1$:
--   $$x_{t+1}=x_t-\frac1\beta\nabla f(x_t).$$
--   Then for every $t\ge2$,
--
--   $$f(x_t)-f(x^*)\le\frac{2\beta\|x_1-x^*\|^2}{t-1}.$$
--
--   This is the basic convergence rate of gradient descent on smooth convex functions: the optimality gap decays like $1/t$, with a constant depending only on the smoothness and on the initial distance to a minimizer, and not on the dimension.
--
--   **Formalization Note** The bound is stated for $t\ge2$: at $t=1$ the right-hand side has denominator $0$. The existence of a minimizer $x^*$ is the book's standing assumption (p. 242). $\beta>0$ is implicit in the step size $\eta=1/\beta$. The gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, and $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.3, p. 267

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Theorem 3.3 (Bubeck, arXiv:1405.4980v2, p. 267): let `f` be convex and β-smooth on `ℝⁿ`
(β > 0) with a minimizer `x*`. Then gradient descent with `η = 1/β`, started at `x₁`, satisfies
`f(x_t) − f(x*) ≤ 2β‖x₁ − x*‖²/(t − 1)` for every `t ≥ 2`. -/
theorem theorem_3_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * ‖x 1 - xstar‖ ^ 2 / ((t : ℝ) - 1) := by sorry

end ConvexOptAlg.SmoothGD
