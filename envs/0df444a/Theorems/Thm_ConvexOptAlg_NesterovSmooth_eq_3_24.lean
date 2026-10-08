-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_eq_3_24
-- name    : ConvexOptAlg.NesterovSmooth.eq_3_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:55:55.712086+00:00
-- url     : https://prove2.me/theorems/4643d4be-2be5-43a5-b7ab-aba0aa65667c
-- title:
--   Eq. (3.24), p. 294 — f(y_{s+1}) − f(x*) ≤ β(x_s − y_{s+1})⊤(x_s − x*) − (β/2)‖x_s − y_{s+1}‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, let $x^*$ be a minimizer of $f$, and let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent for the smooth case. Then for every $s\ge1$,
--
--   $$f(y_{s+1})-f(x^*)\le\beta(x_s-y_{s+1})^\top(x_s-x^*)-\frac\beta2\|x_s-y_{s+1}\|^2.$$
--
--   This is the counterpart of (3.23) with the comparison point $x^*$ in place of $y_s$.
--
--   **Formalization Note** That $x^*$ is a minimizer is the book's standing assumption (p. 242); $\beta>0$ is stated.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, Eq. (3.24), p. 294

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Eq. (3.24) (Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 294): along a run of
Nesterov's accelerated gradient descent on a convex β-smooth `f` with minimizer `x*`, for every
`s ≥ 1`, `f(y_{s+1}) − f(x*) ≤ β(x_s − y_{s+1})⊤(x_s − x*) − (β/2)‖x_s − y_{s+1}‖²`. -/
theorem eq_3_24 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    f (y (s + 1)) - f xstar ≤
      β * ⟪x s - y (s + 1), x s - xstar⟫_ℝ - β / 2 * ‖x s - y (s + 1)‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovSmooth
