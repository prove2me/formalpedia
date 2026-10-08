-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_lemma_6_9
-- name    : ConvexOptAlg.CoordDescent.lemma_6_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:08:38.006205+00:00
-- url     : https://prove2.me/theorems/00310bc2-3097-4e2c-b368-a52d1df66475
-- title:
--   Lemma 6.9, p. 341 — α-strongly convex f w.r.t. ‖·‖ satisfies f(x) − f(x*) ≤ (1/(2α))‖∇f(x)‖²_*
-- statement:
--   Let $E$ be a finite-dimensional real vector space with a norm $\|\cdot\|$, and let $\|\cdot\|_*$ be the dual norm, $\|g\|_*=\sup_{\|y\|\le1}g(y)$ for a linear functional $g$. Let $\alpha>0$ and let $f:E\to\mathbb R$ be differentiable and $\alpha$-strongly convex w.r.t. $\|\cdot\|$, that is $f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{\alpha}{2}\|x-y\|^2$ for all $x,y$. Let $x^*$ be a minimizer of $f$. Then for every $x\in E$,
--
--   $$f(x)-f(x^*)\le\frac{1}{2\alpha}\|\nabla f(x)\|_*^2.$$
--
--   The lemma bounds the optimality gap by the dual norm of the gradient; it is what turns the per-step decrease of a descent method into a linear rate.
--
--   **Formalization Note** $E$ is a finite-dimensional real normed space, $\nabla f(x)$ is the Fréchet derivative $f'(x):E\to\mathbb R$ (continuous linear), and the dual norm is the operator norm of $f'(x)$. The existence of the minimizer $x^*$ is the book's standing assumption (p. 242). The book's proof writes $\|x-y\|_2^2$; the subscript is a slip, the lemma is for an arbitrary norm.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 6.9, p. 341

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Lemma 6.9 (Bubeck, arXiv:1405.4980v2, p. 341): if `f` is α-strongly convex with respect to a norm
`‖·‖` on a finite-dimensional real space and `x*` minimizes `f`, then for every `x`,
`f(x) − f(x*) ≤ (1/(2α)) ‖∇f(x)‖²_*`. The gradient `∇f(x)` is the derivative `f' x : E →L[ℝ] ℝ`
and the dual norm `‖g‖_* = sup_{‖y‖ ≤ 1} g(y)` is the operator norm `‖f' x‖`. -/
theorem lemma_6_9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (f' : E → (E →L[ℝ] ℝ)) (α : ℝ) (hα : 0 < α)
    (hsc : IsStronglyConvexNorm f f' α)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) :
    f x - f xstar ≤ 1 / (2 * α) * ‖f' x‖ ^ 2 := by sorry

end ConvexOptAlg.CoordDescent
