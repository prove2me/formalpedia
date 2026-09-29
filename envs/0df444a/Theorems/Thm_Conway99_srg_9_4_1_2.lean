-- Prove2me | Theorems.Thm_Conway99_srg_9_4_1_2
-- name    : Conway99.srg_9_4_1_2
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:24.367416+00:00
-- url     : https://prove2.me/theorems/26ecef0e-2ff1-409c-8017-7f628d2cf478
-- title:
--   Existence of a strongly regular graph with parameters $(9,4,1,2)$
-- statement:
--   There exists a strongly regular graph with parameters $(9,4,1,2)$: a graph on $9$ vertices, $4$-regular, in which adjacent vertices have exactly one common neighbour and distinct non-adjacent vertices have exactly two.
--
--   A witness is the $3 \times 3$ rook's graph, whose vertices are the cells of a $3 \times 3$ grid with two cells adjacent when they share a row or a column; it is isomorphic to the Paley graph on $9$ vertices and to the graph of the $3$-$3$ duoprism. This is the smallest member of the family $\lambda = 1$, $\mu = 2$ that is known to exist, and it shows that the local conditions of Conway's problem are realisable at some parameter values.
-- source:
--   The 3x3 rook's graph / Paley graph of order 9; see https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem (section 'Related graphs') and https://en.wikipedia.org/wiki/Paley_graph

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem srg_9_4_1_2 : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 9 4 1 2 := by sorry

end Conway99
