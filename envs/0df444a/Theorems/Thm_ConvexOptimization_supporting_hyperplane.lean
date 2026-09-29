-- Prove2me | Theorems.Thm_ConvexOptimization_supporting_hyperplane
-- name    : ConvexOptimization.supporting_hyperplane
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:38:25.28203+00:00
-- url     : https://prove2.me/theorems/3867b747-b4db-412a-9a04-76663013545a
-- title:
--   Supporting hyperplane theorem
-- statement:
--   **The supporting hyperplane theorem:** every boundary point of a convex set admits a supporting hyperplane.
--
--   Let $C \subseteq \mathbb{R}^n$ be convex and let $x_0$ be a point of the boundary of $C$. Then there is a nonzero $a \in \mathbb{R}^n$ with
--
--   $$\langle a, x\rangle \;\le\; \langle a, x_0\rangle \qquad \text{for every } x \in C .$$
--
--   The hyperplane $\{x : \langle a,x\rangle = \langle a,x_0\rangle\}$ touches $C$ at $x_0$ and keeps all of $C$ on one side. There is no uniqueness claim: at a corner of a polytope infinitely many supporting hyperplanes exist.
--
--   Supporting hyperplanes are the geometric form of the subgradient — a supporting hyperplane to the epigraph of $f$ at $(x, f(x))$ is exactly a subgradient of $f$ at $x$ — and they are the mechanism by which a convex set is recovered as the intersection of the halfspaces containing it, which is the converse direction of the separation theory.
--
--   **Formalization Note** Boundary membership is `x₀ ∈ frontier C`; no closedness hypothesis on `C` is needed, since a frontier point of `C` need not belong to `C`, and the conclusion is stated for points of `C` only. Source: B&V §2.5.2, p. 51.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 51, §2.5.2 (supporting hyperplane theorem)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.supporting_hyperplane {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ frontier C) :
    ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∀ x ∈ C, ⟪a, x⟫ ≤ ⟪a, x₀⟫ := by
  sorry
