-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_4
-- name    : ConvexOptAlg.SmoothGD.eq_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:04:41.706991+00:00
-- url     : https://prove2.me/theorems/f8a1dd4b-7514-4ad9-9dc6-457b2d962fde
-- title:
--   Eq. (3.4), p. 267 — a convex β-smooth f satisfies 0 ≤ f(x) − f(y) − ∇f(y)⊤(x − y) ≤ (β/2)‖x − y‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth. Then for all $x,y\in\mathbb R^n$,
--
--   $$0\le f(x)-f(y)-\nabla f(y)^\top(x-y)\le\frac{\beta}{2}\|x-y\|^2.$$
--
--   The lower bound is the first-order characterization of convexity and the upper bound is Lemma 3.4. The book notes that this pair of inequalities characterizes convex $\beta$-smooth functions and is often taken as their definition.
--
--   **Formalization Note** Convexity is Mathlib's `ConvexOn ℝ Set.univ f`; the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (3.4), p. 267

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Eq. (3.4) (Bubeck, arXiv:1405.4980v2, p. 267): for a convex β-smooth `f` on `ℝⁿ` with gradient
map `g`, `0 ≤ f(x) − f(y) − ∇f(y)⊤(x − y) ≤ (β/2)‖x − y‖²` for all `x, y`. -/
theorem eq_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ f x - f y - ⟪g y, x - y⟫_ℝ ∧ f x - f y - ⟪g y, x - y⟫_ℝ ≤ β / 2 * ‖x - y‖ ^ 2 := by sorry

end ConvexOptAlg.SmoothGD
