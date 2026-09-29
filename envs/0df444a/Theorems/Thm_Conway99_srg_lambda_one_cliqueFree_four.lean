-- Prove2me | Theorems.Thm_Conway99_srg_lambda_one_cliqueFree_four
-- name    : Conway99.srg_lambda_one_cliqueFree_four
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T11:14:02.801125+00:00
-- url     : https://prove2.me/theorems/caebea29-a7b5-4d8c-b1b5-c1f46555d18e
-- title:
--   Local linearity: a strongly regular graph with $\lambda = 1$ has no $K_4$
-- statement:
--   **A strongly regular graph with $\lambda = 1$ is $K_4$-free.**
--
--   Let $G$ be strongly regular with parameters $(n, k, 1, \mu)$, so that any two adjacent vertices have exactly one common neighbour. Then $G$ contains no clique on four vertices:
--   $$G \text{ strongly regular with } \lambda = 1 \ \Longrightarrow\ G \text{ is } K_4\text{-free}.$$
--
--   Indeed, if $a, b, c, d$ were four pairwise adjacent vertices, then $c$ and $d$ would be two distinct common neighbours of the adjacent pair $a, b$, contradicting $\lambda = 1$.
--
--   For Conway's 99-graph problem this says that a hypothetical $(99,14,1,2)$ graph has clique number exactly $3$: its maximal cliques are the $231$ triangles that form the lines of the associated partial linear space. The statement is the local-linearity constraint that a search over such graphs must respect, and it holds for every parameter set with $\lambda = 1$, in particular for the realised cases $(9,4,1,2)$ and $(243,22,1,2)$.
--
--   *Formalization note.* The vertex type is an arbitrary finite type with decidable equality, and the parameters $n$, $k$, $\mu$ are unconstrained; only $\lambda = 1$ is used.
-- source:
--   Standard property of locally linear strongly regular graphs; for the (99,14,1,2) case see J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1), and https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem.

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique

open Finset SimpleGraph

namespace Conway99

theorem srg_lambda_one_cliqueFree_four {V : Type} [Fintype V] [DecidableEq V]
    (g : SimpleGraph V) [DecidableRel g.Adj] {n k μ : ℕ} (h : g.IsSRGWith n k 1 μ) :
    g.CliqueFree 4 := by sorry

end Conway99
