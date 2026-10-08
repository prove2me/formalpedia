-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_eq_3_23
-- name    : ConvexOptAlg.NesterovSmooth.eq_3_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:55:44.828428+00:00
-- url     : https://prove2.me/theorems/963f8890-c026-409f-965c-c5bda816133e
-- title:
--   Eq. (3.23), p. 294 — f(y_{s+1}) − f(y_s) ≤ β(x_s − y_{s+1})⊤(x_s − y_s) − (β/2)‖x_s − y_{s+1}‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, and let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent for the smooth case. Then for every $s\ge1$,
--
--   $$\begin{aligned}f(y_{s+1})-f(y_s)&\le\nabla f(x_s)^\top(x_s-y_s)-\frac1{2\beta}\|\nabla f(x_s)\|^2\\&=\beta(x_s-y_{s+1})^\top(x_s-y_s)-\frac\beta2\|x_s-y_{s+1}\|^2.\end{aligned}$$
--
--   The inequality compares two consecutive points of the primary sequence; the equality rewrites the gradient through $\nabla f(x_s)=\beta(x_s-y_{s+1})$.
--
--   **Formalization Note** Both the inequality and the equality are asserted, as a conjunction. $\beta>0$ is stated.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, Eq. (3.23), p. 294

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Eq. (3.23) (Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 294): along a run of
Nesterov's accelerated gradient descent on a convex β-smooth `f`, for every `s ≥ 1`,
`f(y_{s+1}) − f(y_s) ≤ ∇f(x_s)⊤(x_s − y_s) − (1/(2β))‖∇f(x_s)‖²`
`= β(x_s − y_{s+1})⊤(x_s − y_s) − (β/2)‖x_s − y_{s+1}‖²`. Both the inequality and the equality
are asserted. -/
theorem eq_3_23 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    f (y (s + 1)) - f (y s) ≤ ⟪g (x s), x s - y s⟫_ℝ - 1 / (2 * β) * ‖g (x s)‖ ^ 2 ∧
      ⟪g (x s), x s - y s⟫_ℝ - 1 / (2 * β) * ‖g (x s)‖ ^ 2 =
        β * ⟪x s - y (s + 1), x s - y s⟫_ℝ - β / 2 * ‖x s - y (s + 1)‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovSmooth
