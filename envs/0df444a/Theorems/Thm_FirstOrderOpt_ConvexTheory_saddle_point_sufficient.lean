-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_saddle_point_sufficient
-- name    : FirstOrderOpt.ConvexTheory.saddle_point_sufficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:54:58.517662+00:00
-- url     : https://prove2.me/theorems/7990efb0-3b0d-4dc4-a8df-dc8789b89631
-- title:
--   Theorem 2.7(a) — saddle-point sufficiency
-- statement:
--   Let $x^* \in X$. **Theorem 2.7(a).** If $x^*$ can be extended, by some $\lambda^* \ge 0$ and
--   $y^* \in \mathbb{R}^p$, to a saddle point of the Lagrangian on $X \times \{\lambda \ge 0\}
--   \times \mathbb{R}^p$:
--   $$L(x,\lambda^*,y^*) \ge L(x^*,\lambda^*,y^*) \ge L(x^*,\lambda,y) \quad \forall (x \in X,\
--   \lambda \ge 0,\ y \in \mathbb{R}^p),$$
--   then $x^*$ is optimal for (2.3.16) — meaning $x^*$ is feasible and $f(x^*) \le f(x)$ for
--   every feasible $x$.
--
--   This is the first of two optimality certificates strong duality yields: a saddle point of
--   the Lagrangian at $x^*$ is a checkable witness that $x^*$ solves (2.3.16), with no
--   convexity needed for this direction.
--
--   **Formalization Note.** The conclusion "$x^*$ optimal" is unpacked as the conjunction of
--   $x^*$'s own feasibility ($g_i(x^*)\le 0$, $h_j(x^*)=0$) and its minimality among feasible
--   points, since the book's proof derives feasibility of $x^*$ from the right-hand saddle
--   inequality (taking $\sup_{\lambda\ge0,y}L(x^*,\lambda,y)$) before concluding minimality.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 41, Theorem 2.7(a)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian

namespace FirstOrderOpt.ConvexTheory

/-- Theorem 2.7(a) (saddle-point sufficiency). If `x* ∈ X` extends, with `λ* ≥ 0` and `y*`, to
a saddle point of the Lagrangian on `X × {λ ≥ 0} × ℝᵖ`, then `x*` is feasible and optimal for
(2.3.16). -/
theorem saddle_point_sufficient {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hsaddle1 : ∀ x ∈ X, lagrangian f g h xstar lamStar yStar ≤ lagrangian f g h x lamStar yStar)
    (hsaddle2 : ∀ lam : Fin m → ℝ, ∀ y : Fin p → ℝ, (∀ i, 0 ≤ lam i) →
        lagrangian f g h xstar lam y ≤ lagrangian f g h xstar lamStar yStar) :
    (∀ i, g i xstar ≤ 0) ∧ (∀ j, h j xstar = 0) ∧
      ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x := by sorry

end FirstOrderOpt.ConvexTheory
