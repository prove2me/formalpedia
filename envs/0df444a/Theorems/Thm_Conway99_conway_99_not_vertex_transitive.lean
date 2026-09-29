-- Prove2me | Theorems.Thm_Conway99_conway_99_not_vertex_transitive
-- name    : Conway99.conway_99_not_vertex_transitive
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:15:09.972716+00:00
-- url     : https://prove2.me/theorems/2cbb1240-c213-4d7d-aed2-4c59321fe36e
-- title:
--   Wilbrink (1984): a $(99,14,1,2)$ graph is not vertex-transitive
-- statement:
--   No strongly regular graph with parameters $(99,14,1,2)$ is vertex-transitive: if $g$ is such a graph, then it is not the case that for every pair of vertices $v, w$ there is a graph automorphism of $g$ carrying $v$ to $w$.
--
--   This is Wilbrink's theorem. In particular a hypothetical $99$-graph cannot be a Cayley graph, which rules out the group-theoretic constructions that produce most known strongly regular graphs — including the two realised members of the family $\lambda = 1$, $\mu = 2$, namely the Paley graph on $9$ vertices and the Berlekamp–van Lint–Seidel graph. The statement is a genuine restriction rather than a vacuous one only in the sense that existence is open; proving it does not require knowing whether such a graph exists.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel, EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://research.tue.nl/files/2449333/256699.pdf ; as summarised in https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

namespace Conway99

theorem conway_99_not_vertex_transitive {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    ¬ ∀ v w : V, ∃ f : g ≃g g, f v = w := by sorry

end Conway99
