-- Prove2me | Theorems.Thm_Conway99_conway_99
-- name    : Conway99.conway_99
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T16:15:19.958889+00:00
-- url     : https://prove2.me/theorems/7bc34ad9-a7f2-480e-ac84-4cfe4cd5042a
-- title:
--   Conway's 99-graph problem: a strongly regular graph with parameters $(99,14,1,2)$
-- statement:
--   **Conway's 99-graph problem.** Does there exist an undirected graph on $99$ vertices in which every two adjacent vertices have exactly one common neighbour and every two distinct non-adjacent vertices have exactly two common neighbours? Equivalently: every edge lies in a unique triangle, and every non-adjacent pair is the pair of opposite corners of a unique quadrilateral. Such a graph is necessarily $14$-regular, i.e. strongly regular with parameters $(99,14,1,2)$.
--
--   The statement asserts the existence of a finite type $\alpha$ carrying a simple graph $g$ with $\mathrm{IsSRGWith}\ g\ 99\ 14\ 1\ 2$, and is Mathlib's `proof_wanted conway_99` verbatim. The problem is open: no such graph is known, and no non-existence proof is known. John Horton Conway offered \$1000 for a solution. A disproof — a proof that no such graph exists — resolves the problem just as well as a construction.
-- source:
--   J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1); statement taken verbatim from Mathlib's `proof_wanted conway_99` in Mathlib/Combinatorics/SimpleGraph/StronglyRegular.lean; see also https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem conway_99 : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 99 14 1 2 := by sorry

end Conway99
