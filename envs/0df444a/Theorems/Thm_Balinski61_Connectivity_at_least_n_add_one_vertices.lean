-- Prove2me | Theorems.Thm_Balinski61_Connectivity_at_least_n_add_one_vertices
-- name    : Balinski61.Connectivity.at_least_n_add_one_vertices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:23.874987+00:00
-- url     : https://prove2.me/theorems/afc78c1f-173b-4f42-af73-4df3e4621ae5
-- title:
--   p. 432, proof of the THEOREM — S has at least n + 1 vertices
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Then $S$ has at least $n+1$ vertices:
--   $$\bigl|\operatorname{ext} S\bigr|\ \ge\ n+1.$$
--
--   This is the first sentence of the proof of the THEOREM ("for otherwise it would lie within an $(n-1)$-dimensional hyperplane") and is the point-count half of the statement that $G(S)$ is $n$-tuply connected.
--
--   **Formalization Note** The count is the extended cardinality `Set.encard` of the set of extreme points, so no finiteness assumption is needed to state it.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, proof of the THEOREM, first sentence

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem at_least_n_add_one_vertices (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    (n : ℕ∞) + 1 ≤ (Set.extremePoints ℝ (Hirsch.Hpoly a b)).encard := by sorry

end Balinski61.Connectivity
