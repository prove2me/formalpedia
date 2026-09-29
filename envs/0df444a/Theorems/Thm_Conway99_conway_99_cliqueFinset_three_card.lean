-- Prove2me | Theorems.Thm_Conway99_conway_99_cliqueFinset_three_card
-- name    : Conway99.conway_99_cliqueFinset_three_card
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:50.742732+00:00
-- url     : https://prove2.me/theorems/8ef2c9b9-d339-44ff-bfb5-2490907f4d1d
-- title:
--   A $99$-graph has exactly $231$ triangles
-- statement:
--   Any strongly regular graph with parameters $(99,14,1,2)$ contains exactly $231$ triangles, where a triangle is a $3$-element clique.
--
--   Since $\lambda = 1$, every edge lies in exactly one triangle, and every triangle contains three edges, so the number of triangles is $693/3 = 231$; equivalently $99 \cdot 14 \cdot 1 / 6$. A hypothetical $99$-graph is therefore a partial linear space with $99$ points and $231$ lines of size $3$, each point on $7$ lines.
-- source:
--   Triangle count from lambda = 1 for the parameters of Conway's 99-graph problem; https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Conway99

theorem conway_99_cliqueFinset_three_card {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    (g.cliqueFinset 3).card = 231 := by sorry

end Conway99
