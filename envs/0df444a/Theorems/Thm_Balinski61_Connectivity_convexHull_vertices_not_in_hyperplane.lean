-- Prove2me | Theorems.Thm_Balinski61_Connectivity_convexHull_vertices_not_in_hyperplane
-- name    : Balinski61.Connectivity.convexHull_vertices_not_in_hyperplane
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:14.413807+00:00
-- url     : https://prove2.me/theorems/a846b99e-7048-4232-8730-417fe47e51fc
-- title:
--   p. 432 — S is the convex hull of its finitely many vertices and lies within no hyperplane
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Then $S$ has finitely many vertices (extreme points), $S$ is their convex hull,
--   $$S=\operatorname{conv}\bigl(\operatorname{ext} S\bigr),$$
--   and $S$ lies within no $(n-1)$-dimensional hyperplane: for every nonzero $c\in\mathbb R^n$ and every $d\in\mathbb R$ some $x\in S$ has $\langle c,x\rangle\neq d$.
--
--   Balinski states this right after system (1) ("This assures us that the set $S$ is just the convex hull of its vertices, and that it lies within no $(n-1)$-dimensional hyperplane"), citing Tucker. It turns the algebraic assumptions into the geometric picture of a full-dimensional polytope on which the proof of the THEOREM runs; the second clause is used in case (c) of that proof.
--
--   **Formalization Note** Finiteness of the vertex set is not in the quoted sentence; it is what "form a graph" requires (graphs are finite on p. 431) and is stated here explicitly. A hyperplane is a set $\{x:\langle c,x\rangle=d\}$ with $c\neq0$.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, the assumptions on system (1) and the sentence following them

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem convexHull_vertices_not_in_hyperplane (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite ∧
      convexHull ℝ (Set.extremePoints ℝ (Hirsch.Hpoly a b)) = Hirsch.Hpoly a b ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (d : ℝ), c ≠ 0 →
        ∃ x ∈ Hirsch.Hpoly a b, ⟪c, x⟫ ≠ d := by sorry

end Balinski61.Connectivity
