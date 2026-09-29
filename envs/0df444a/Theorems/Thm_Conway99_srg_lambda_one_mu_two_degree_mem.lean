-- Prove2me | Theorems.Thm_Conway99_srg_lambda_one_mu_two_degree_mem
-- name    : Conway99.srg_lambda_one_mu_two_degree_mem
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:12.426202+00:00
-- url     : https://prove2.me/theorems/3f3f0009-f6b6-4594-893d-cd55a270faa8
-- title:
--   Only five feasible degrees: $k \in \{2, 4, 14, 22, 112, 994\}$
-- statement:
--   Let $g$ be a strongly regular graph with parameters $(n, k, 1, 2)$ on a finite vertex set with at least two vertices. Then
--
--   $$k \in \{2, 4, 14, 22, 112, 994\}.$$
--
--   Together with the counting identity $2n = k^2 + 2$ these degrees correspond to the parameter tuples $(3,2,1,2)$ (the triangle $K_3$, where the condition on non-adjacent pairs is vacuous), $(9,4,1,2)$, $(99,14,1,2)$, $(243,22,1,2)$, $(6273,112,1,2)$ and $(494019,994,1,2)$. Beyond the complete case, the restriction comes from the integrality conditions: the adjacency matrix has eigenvalues $k$ and the two roots of $x^2 + x - (k-2) = 0$, so $4k - 7$ must be a perfect square $t^2$, and the multiplicities of the two non-principal eigenvalues are integers only when $t$ divides $63$. This is the classical argument showing that the family $\lambda = 1$, $\mu = 2$ contains only five non-degenerate feasible parameter tuples, two of which are realised and three of which — including $(99,14,1,2)$ — are open.
-- source:
--   Classical feasibility (integrality) conditions for strongly regular graphs with lambda = 1, mu = 2; the list of five feasible parameter tuples is as recorded in https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem (section 'Related graphs'), citing Makhnev & Minakova, Discrete Math. Appl. 14 (2004), no. 2

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem srg_lambda_one_mu_two_degree_mem {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k : ℕ} (h : g.IsSRGWith n k 1 2) (hn : 1 < n) :
    k = 2 ∨ k = 4 ∨ k = 14 ∨ k = 22 ∨ k = 112 ∨ k = 994 := by sorry

end Conway99
