-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_theorem_3_19
-- name    : ConvexOptAlg.NesterovSmooth.theorem_3_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:31.607475+00:00
-- url     : https://prove2.me/theorems/08f18b5c-2c2a-47ef-b3e8-c696248f2f3c
-- title:
--   Theorem 3.19, p. 294 — Nesterov's accelerated gradient descent on a convex β-smooth f satisfies f(y_t) − f(x*) ≤ 2β‖x₁ − x*‖²/t²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, and let $x^*$ be a minimizer of $f$. Let $\lambda_0=0$, $\lambda_t=\frac{1+\sqrt{1+4\lambda_{t-1}^2}}2$ and $\gamma_t=\frac{1-\lambda_t}{\lambda_{t+1}}$, and let $(x_t),(y_t)$ be generated from an arbitrary initial point $x_1=y_1$ by
--
--   $$y_{t+1}=x_t-\frac1\beta\nabla f(x_t),\qquad x_{t+1}=(1-\gamma_t)\,y_{t+1}+\gamma_t\,y_t\qquad(t\ge1).$$
--
--   Then for every $t\ge1$,
--
--   $$f(y_t)-f(x^*)\le\frac{2\beta\|x_1-x^*\|^2}{t^2}.$$
--
--   This is the accelerated $O(1/t^2)$ rate of Nesterov's method for smooth convex optimization, which improves on the $O(1/t)$ rate of plain gradient descent (Theorem 3.3) and matches, up to a constant factor, the black-box lower bound of Theorem 3.14.
--
--   **Formalization Note** The gradient is an explicit map $g$ with $g(x)=\nabla f(x)$; convexity is `ConvexOn ℝ Set.univ f` and $f$ is defined on all of $\mathbb R^n$ (the unconstrained setting of §3.7). That $x^*$ is a minimizer is the book's standing assumption (p. 242); $\beta>0$ is implicit in the step $1/\beta$ and is stated. The bound is asserted for every $t\ge1$: the page's proof covers $t\ge2$, and at $t=1$ the claim follows from the quadratic upper bound (3.4). The algorithm uses $\gamma_t$ in both coefficients of the $x$-update (the page's $\gamma_s$ is a misprint).
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.19, p. 294 (algorithm of §3.7.2, pp. 293–294)

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Theorem 3.19 (Bubeck, arXiv:1405.4980v2, p. 294): let `f` be convex and β-smooth on `ℝⁿ`
(β > 0) with gradient map `g` and a minimizer `x*`. Then every run of Nesterov's accelerated
gradient descent (§3.7.2) satisfies `f(y_t) − f(x*) ≤ 2β‖x₁ − x*‖²/t²` for every `t ≥ 1`. -/
theorem theorem_3_19 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xstar ≤ 2 * β * ‖x 1 - xstar‖ ^ 2 / (t : ℝ) ^ 2 := by sorry

end ConvexOptAlg.NesterovSmooth
