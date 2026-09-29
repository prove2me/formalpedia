-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_separation_point_closed
-- name    : FirstOrderOpt.ConvexTheory.separation_point_closed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T17:35:43.139182+00:00
-- url     : https://prove2.me/theorems/00a20847-9748-405d-9cb6-ef99501f47ea
-- title:
--   Theorem 2.1 — separation of a point from a closed convex set
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be a nonempty closed convex set and let $y \notin X$. Then
--   there is a nonzero $w \in \mathbb{R}^n$ with
--   $$\langle w, y\rangle < \langle w, x\rangle \quad \text{for every } x \in X.$$
--   This is the basic separation theorem of convex analysis: a point outside a closed convex
--   set can be strictly separated from it by a hyperplane. Lan's proof projects $y$ onto $X$
--   and takes $w := y - \operatorname{Proj}_X(y)$.
--
--   **Formalization Note.** Stated over `EuclideanSpace ℝ (Fin n)`; `X` nonempty and closed are
--   both used (closedness for the projection to exist, nonemptiness for the projection to be
--   defined at all). This is the finite-dimensional special case of Mathlib's
--   `geometric_hahn_banach_point_closed`; a solution-quality development may cite that lemma
--   directly once the milestone's own proof is filled in, rather than re-deriving the
--   projection argument.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 25, Theorem 2.1

import Mathlib

namespace FirstOrderOpt.ConvexTheory

open scoped RealInnerProductSpace

/-- Theorem 2.1 (separation of a point from a closed convex set). If `X ⊆ ℝⁿ` is a nonempty
closed convex set and `y ∉ X`, there is a nonzero `w` with `⟪w, y⟫ < ⟪w, x⟫` for every `x ∈ X`. -/
theorem separation_point_closed {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXne : X.Nonempty) (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∉ X) :
    ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 ∧ ∀ x ∈ X, ⟪w, y⟫ < ⟪w, x⟫ := by sorry

end FirstOrderOpt.ConvexTheory
