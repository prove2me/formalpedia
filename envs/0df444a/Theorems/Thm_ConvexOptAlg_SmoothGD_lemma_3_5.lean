-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_5
-- name    : ConvexOptAlg.SmoothGD.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:05:05.27784+00:00
-- url     : https://prove2.me/theorems/e0efe0ca-9e91-4241-9ae1-08ac97622417
-- title:
--   Lemma 3.5, p. 268 — if (3.4) holds, then f(x) − f(y) ≤ ∇f(x)⊤(x − y) − (1/(2β))‖∇f(x) − ∇f(y)‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable, let $\beta>0$, and suppose that (3.4) holds: for all $x,y\in\mathbb R^n$,
--   $$0\le f(x)-f(y)-\nabla f(y)^\top(x-y)\le\frac\beta2\|x-y\|^2.$$
--   Then for all $x,y\in\mathbb R^n$,
--
--   $$f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{1}{2\beta}\|\nabla f(x)-\nabla f(y)\|^2.$$
--
--   This sharpens the basic subgradient inequality $f(x)-f(y)\le\nabla f(x)^\top(x-y)$ under smoothness, and shows that (3.4) implies co-coercivity of the gradient (3.6).
--
--   **Formalization Note** The hypothesis is the two-sided inequality (3.4), as in the book, not "convex and $\beta$-smooth". The gradient is an explicit map $g$ with $g(x)=\nabla f(x)$; $\beta>0$ is implicit in the page, which divides by $\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.5, p. 268

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Lemma 3.5 (Bubeck, arXiv:1405.4980v2, p. 268): let `f : ℝⁿ → ℝ` be differentiable with
gradient map `g`, `β > 0`, and suppose (3.4) holds for all `x, y`:
`0 ≤ f(x) − f(y) − ∇f(y)⊤(x − y) ≤ (β/2)‖x − y‖²`. Then for all `x, y`,
`f(x) − f(y) ≤ ∇f(x)⊤(x − y) − (1/(2β))‖∇f(x) − ∇f(y)‖²`.
The hypothesis is the two-sided inequality (3.4), as printed, not convexity and β-smoothness. -/
theorem lemma_3_5 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (h34 : ∀ x y : EuclideanSpace ℝ (Fin n),
      0 ≤ f x - f y - ⟪g y, x - y⟫_ℝ ∧ f x - f y - ⟪g y, x - y⟫_ℝ ≤ β / 2 * ‖x - y‖ ^ 2)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x - f y ≤ ⟪g x, x - y⟫_ℝ - 1 / (2 * β) * ‖g x - g y‖ ^ 2 := by sorry

end ConvexOptAlg.SmoothGD
