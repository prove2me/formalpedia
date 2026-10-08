-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_6
-- name    : ConvexOptAlg.SmoothGD.eq_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:05:18.569385+00:00
-- url     : https://prove2.me/theorems/f8f315f6-3765-4a76-b5f6-bcef27e0c2c5
-- title:
--   Eq. (3.6), p. 269 — the gradient of a convex β-smooth f is (1/β)-co-coercive
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$. Then for all $x,y\in\mathbb R^n$,
--
--   $$(\nabla f(x)-\nabla f(y))^\top(x-y)\ge\frac1\beta\|\nabla f(x)-\nabla f(y)\|^2.$$
--
--   This co-coercivity of the gradient is what makes the distance from the gradient descent iterates to a minimizer non-increasing in the proof of Theorem 3.3.
--
--   **Formalization Note** The gradient is an explicit map $g$; $\beta>0$ is implicit in the page, which divides by $\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (3.6), §3.2, proof of Theorem 3.3, p. 269

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Eq. (3.6) (Bubeck, arXiv:1405.4980v2, p. 269): the gradient of a convex β-smooth `f` on `ℝⁿ`
(β > 0) is co-coercive, `(∇f(x) − ∇f(y))⊤(x − y) ≥ (1/β)‖∇f(x) − ∇f(y)‖²` for all `x, y`. -/
theorem eq_3_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    1 / β * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by sorry

end ConvexOptAlg.SmoothGD
