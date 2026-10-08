-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_thm_6_7_coord_step
-- name    : ConvexOptAlg.CoordDescent.thm_6_7_coord_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:08:49.013098+00:00
-- url     : https://prove2.me/theorems/2e435a24-c307-4ca7-ae96-484f2b8c7c2a
-- title:
--   §6.4.1, proof of Theorem 6.7, p. 340 — one coordinate step decreases f by at least (∇_i f(x))²/(2β_i)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable and directionally smooth with constants $\beta_1,\dots,\beta_n$, i.e. $|\nabla_i f(x+ue_i)-\nabla_i f(x)|\le\beta_i|u|$ for all $i$, $x$, $u$. Fix a coordinate $i$ with $\beta_i>0$. Then for every $x\in\mathbb R^n$,
--
--   $$f\Big(x-\frac{1}{\beta_i}\nabla_i f(x)e_i\Big)-f(x)\le-\frac{1}{2\beta_i}\big(\nabla_i f(x)\big)^2.$$
--
--   This is inequality (3.5) applied to the $\beta_i$-smooth one-variable function $u\mapsto f(x+ue_i)$: a step of length $1/\beta_i$ along coordinate $i$ decreases $f$ by at least the squared partial derivative over $2\beta_i$.
--
--   **Formalization Note** $\beta_i>0$ is added because the step is $1/\beta_i$. Convexity of $f$, a standing assumption of §6.4, is not needed for this inequality and is not assumed.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.4.1, proof of Theorem 6.7, first display, p. 340

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Proof of Theorem 6.7, first display (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 340): applying (3.5) to
the βᵢ-smooth function `u ↦ f(x + u eᵢ)`,
`f(x − (1/βᵢ) ∇ᵢ f(x) eᵢ) − f(x) ≤ −(1/(2βᵢ)) (∇ᵢ f(x))²`, for every coordinate `i` and point `x`.
Here `f` is coordinate-wise smooth with constants `β` and gradient map `g` (`∇ᵢ f(x) = g x i`),
and `βᵢ > 0` (the step is `1/βᵢ`). No convexity is needed. -/
theorem thm_6_7_coord_step {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ)
    (hsm : IsCoordSmooth f g β) (i : Fin n) (hβi : 0 < β i) (x : EuclideanSpace ℝ (Fin n)) :
    f (rcdStep β g x i) - f x ≤ -(1 / (2 * β i)) * g x i ^ 2 := by sorry

end ConvexOptAlg.CoordDescent
