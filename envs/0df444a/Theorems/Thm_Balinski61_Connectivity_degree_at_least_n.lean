-- Prove2me | Theorems.Thm_Balinski61_Connectivity_degree_at_least_n
-- name    : Balinski61.Connectivity.degree_at_least_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:33.04714+00:00
-- url     : https://prove2.me/theorems/84e068c7-52d8-41a7-bb5e-6c38fd5c2c06
-- title:
--   p. 432, preliminary remark — every point of G(S) has degree at least n
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Let $G(S)$ be the graph of the vertices and edges of $S$. Then every vertex $v$ of $S$ lies on at least $n$ edges:
--   $$\deg_{G(S)}(v)=\bigl|\{w : [v,w] \text{ is an edge of } S\}\bigr|\ \ge\ n .$$
--
--   Balinski calls this the "obvious statement" made as a preliminary remark before the THEOREM. It is the necessary condition on degrees that $n$-tuple connectivity implies, recorded separately for the polytope.
--
--   **Formalization Note** The degree is the extended cardinality `Set.encard` of the neighbour set of $v$ in `polyGraph S`.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, preliminary remark before the THEOREM

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem degree_at_least_n (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b)
    (v : Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    (n : ℕ∞) ≤ ((polyGraph (Hirsch.Hpoly a b)).neighborSet v).encard := by sorry

end Balinski61.Connectivity
