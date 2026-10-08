-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_5
-- name    : ConvexOptAlg.SmoothGD.eq_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:04:51.079636+00:00
-- url     : https://prove2.me/theorems/b284c842-54b8-45c3-b943-5867b9cd5bee
-- title:
--   Eq. (3.5), p. 267 — a gradient step of length 1/β decreases f by at least ‖∇f(x)‖²/(2β)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$. Then for every $x\in\mathbb R^n$,
--
--   $$f\Bigl(x-\frac1\beta\nabla f(x)\Bigr)-f(x)\le-\frac{1}{2\beta}\|\nabla f(x)\|^2.$$
--
--   This inequality measures the improvement made by one step of gradient descent with step size $1/\beta$, and is the starting point of the analysis of Theorem 3.3.
--
--   **Formalization Note** Convexity is retained from the source context preceding (3.4). The condition $\beta>0$ is implicit in the page, which divides by $\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (3.5), p. 267

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Eq. (3.5) (Bubeck, arXiv:1405.4980v2, p. 267): one gradient step of length `1/β` on a
convex β-smooth `f` (β > 0) decreases `f` by at least `‖∇f(x)‖²/(2β)`:
`f(x − (1/β)∇f(x)) − f(x) ≤ −(1/(2β))‖∇f(x)‖²`. -/
theorem eq_3_5 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - (1 / β) • g x) - f x ≤ -(1 / (2 * β)) * ‖g x‖ ^ 2 := by sorry

end ConvexOptAlg.SmoothGD
