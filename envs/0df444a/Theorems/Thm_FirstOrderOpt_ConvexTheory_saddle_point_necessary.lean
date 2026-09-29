-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_saddle_point_necessary
-- name    : FirstOrderOpt.ConvexTheory.saddle_point_necessary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:55:21.068815+00:00
-- url     : https://prove2.me/theorems/ef39f39d-d634-4553-a7b6-22ee3507ad51
-- title:
--   Theorem 2.7(b) — saddle-point necessity under Slater's condition
-- statement:
--   **Theorem 2.7(b).** If $x^* \in X$ is optimal for the convex program (2.3.16), and
--   (2.3.16) satisfies Slater's condition ($\exists \bar x \in \operatorname{int} X$ with $g(\bar
--   x) < 0$, $h(\bar x)=0$), then $x^*$ can be extended, by some $\lambda^* \ge 0$ and $y^* \in
--   \mathbb{R}^p$, to a saddle point of the Lagrangian on $X \times \{\lambda \ge 0\} \times
--   \mathbb{R}^p$.
--
--   This is the converse of Theorem 2.7(a): under a constraint qualification, every optimal
--   point *is* a saddle point of some Lagrangian, obtained directly from strong duality
--   (Theorem 2.6) applied at $x^*$.
--
--   **Formalization Note.** $h$ affine is again represented via explicit witnesses $w, b$ as in
--   `strong_duality`. $x^*$'s optimality is stated in the same unpacked form as the conclusion
--   of `saddle_point_sufficient` (feasible and minimal among feasible points), so the two
--   theorems are literal converses of each other once specialized to the same $X, f, g, h$.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 41, Theorem 2.7(b)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian

namespace FirstOrderOpt.ConvexTheory

/-- Theorem 2.7(b) (saddle-point necessity). If `x*` is optimal for the convex, Slater-feasible
program (2.3.16), then `x*` extends, with some `λ* ≥ 0` and `y*`, to a saddle point of the
Lagrangian on `X × {λ ≥ 0} × ℝᵖ`. -/
theorem saddle_point_necessary {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_int : barx ∈ interior X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hxstar_feas_g : ∀ i, g i xstar ≤ 0) (hxstar_feas_h : ∀ j, h j xstar = 0)
    (hxstar_opt : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      (∀ x ∈ X, lagrangian f g h xstar lamStar yStar ≤ lagrangian f g h x lamStar yStar) ∧
      (∀ lam : Fin m → ℝ, ∀ y : Fin p → ℝ, (∀ i, 0 ≤ lam i) →
        lagrangian f g h xstar lam y ≤ lagrangian f g h xstar lamStar yStar) := by sorry

end FirstOrderOpt.ConvexTheory
