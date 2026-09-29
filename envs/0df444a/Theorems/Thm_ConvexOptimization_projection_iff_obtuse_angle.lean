-- Prove2me | Theorems.Thm_ConvexOptimization_projection_iff_obtuse_angle
-- name    : ConvexOptimization.projection_iff_obtuse_angle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:31:45.422606+00:00
-- url     : https://prove2.me/theorems/aac660a6-edbf-491c-90ff-56f4949dcf52
-- title:
--   Characterization of Euclidean projection
-- statement:
--   **Characterization of the Euclidean projection onto a convex set:** the error vector makes a non-acute angle with every feasible direction.
--
--   Let $C \subseteq \mathbb{R}^n$ be convex, let $x_0 \in \mathbb{R}^n$ and let $z \in C$. Then
--
--   $$\bigl(\lVert x_0 - z\rVert_2 \le \lVert x_0 - w\rVert_2 \ \text{ for all } w \in C\bigr) \qquad\Longleftrightarrow\qquad \langle x_0 - z,\ w - z\rangle \le 0 \ \text{ for all } w \in C .$$
--
--   The left side says $z$ is a nearest point of $C$ to $x_0$; the right side says the angle between the error $x_0 - z$ and any direction $w - z$ pointing into $C$ is at least $90^{\circ}$.
--
--   The criterion turns a minimization over $C$ into a family of linear inequalities, which is what makes projections computable and is the standard entry point to the theory of projection algorithms and separating hyperplanes. It is the special case of the first-order optimality criterion (4.21) for the objective $w \mapsto \lVert x_0 - w\rVert_2^2$.
--
--   **Formalization Note** The statement is an iff between two universally quantified conditions on $C$, with no existence or uniqueness claim about the projection, so no completeness or closedness hypothesis on $C$ is needed. Norms and inner products are those of `EuclideanSpace ℝ (Fin n)`. Source: B&V §8.1.1, p. 398, via eq. (4.21).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 397-398, §8.1.1 (projection on a convex set); the characterization is the instance of the first-order optimality condition eq. (4.21), p. 139, for the projection problem

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.projection_iff_obtuse_angle {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C)
    (x₀ z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ C) :
    (∀ w ∈ C, ‖x₀ - z‖ ≤ ‖x₀ - w‖) ↔ ∀ w ∈ C, ⟪x₀ - z, w - z⟫ ≤ 0 := by
  sorry
