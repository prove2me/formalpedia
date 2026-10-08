-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_4
-- name    : ConvexOptAlg.SmoothGD.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:04:26.056577+00:00
-- url     : https://prove2.me/theorems/f3fdb7a4-d291-498c-b59a-f8de687edfd2
-- title:
--   Lemma 3.4, p. 267 — a β-smooth f satisfies |f(x) − f(y) − ∇f(y)⊤(x − y)| ≤ (β/2)‖x − y‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\beta$-smooth, i.e. differentiable with $\beta$-Lipschitz gradient $\nabla f$. Then for all $x,y\in\mathbb R^n$,
--
--   $$\bigl|f(x)-f(y)-\nabla f(y)^\top(x-y)\bigr|\le\frac{\beta}{2}\|x-y\|^2.$$
--
--   This is the two-sided quadratic bound on the error of the first-order Taylor approximation; no convexity is assumed. Its upper half is the descent lemma used to measure the progress of one gradient step.
--
--   **Formalization Note** The gradient is an explicit map $g$ with $g(x)=\nabla f(x)$ for every $x$; $\beta\ge0$ is included because a Lipschitz constant is non-negative, including when $n=0$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.4, p. 267

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Lemma 3.4 (Bubeck, arXiv:1405.4980v2, p. 267): for a β-smooth `f` on `ℝⁿ` with gradient map
`g`, `|f(x) − f(y) − ∇f(y)⊤(x − y)| ≤ (β/2)‖x − y‖²` for all `x, y`. No convexity. -/
theorem lemma_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    |f x - f y - ⟪g y, x - y⟫_ℝ| ≤ β / 2 * ‖x - y‖ ^ 2 := by sorry

end ConvexOptAlg.SmoothGD
