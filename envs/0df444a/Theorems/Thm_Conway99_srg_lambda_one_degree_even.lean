-- Prove2me | Theorems.Thm_Conway99_srg_lambda_one_degree_even
-- name    : Conway99.srg_lambda_one_degree_even
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:13:59.588898+00:00
-- url     : https://prove2.me/theorems/ddfb4e64-d09e-4662-9c55-24aefbbd17c6
-- title:
--   Local linearity: $\lambda = 1$ forces the degree $k$ to be even
-- statement:
--   Let $g$ be a strongly regular graph on a nonempty finite vertex set with parameters $(n, k, 1, \mu)$ for an arbitrary $\mu$, so that every edge lies in exactly one triangle. Then the degree $k$ is even.
--
--   The reason is local: for a vertex $v$, each neighbour $w$ of $v$ has exactly one neighbour inside $N(v)$, namely the unique common neighbour of $v$ and $w$. Hence the graph induced on the $k$-element set $N(v)$ is $1$-regular, i.e. a perfect matching, and a finite graph admitting a perfect matching has an even number of vertices. Graphs with $\lambda = 1$ are called locally linear for exactly this reason; for the parameters of Conway's problem the neighbourhood of every vertex is a perfect matching on $14$ vertices, i.e. $7$ disjoint edges.
-- source:
--   Local linearity of strongly regular graphs with lambda = 1; https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem and https://en.wikipedia.org/wiki/Locally_linear_graph

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem srg_lambda_one_degree_even {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k m : ℕ} (h : g.IsSRGWith n k 1 m) (hn : 0 < n) :
    Even k := by sorry

end Conway99
