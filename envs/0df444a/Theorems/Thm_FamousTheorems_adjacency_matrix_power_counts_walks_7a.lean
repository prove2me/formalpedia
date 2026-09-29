-- Prove2me | Theorems.Thm_FamousTheorems_adjacency_matrix_power_counts_walks_7a
-- name    : FamousTheorems.adjacency_matrix_power_counts_walks_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:38.277033+00:00
-- url     : https://prove2.me/theorems/ddbed621-283c-4dad-8d19-9ef3f227b4c3
-- title:
--   Powers of the adjacency matrix count walks
-- statement:
--   **Powers of the adjacency matrix count walks.** Let $G$ be a finite simple graph with adjacency matrix $A$. For all vertices $u,v$ and every $n\ge0$, the $(u,v)$ entry of $A^n$ is the number of walks of length $n$ from $u$ to $v$ in $G$.
--
--   This is the basic link between graph theory and linear algebra. It leads to spectral graph theory, where eigenvalues of $A$ control walk counts. It gives the number of closed walks as $\operatorname{tr}A^n=\sum\lambda_i^n$, the number of triangles as $\operatorname{tr}A^3/6$, and the use of eigenvalues to study expansion and random walks.
--
--   **Formalization note.** Mathlib's `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`. `G.adjMatrix α` is the adjacency matrix with entries in any semiring $\alpha$, and the count of walks is cast into $\alpha$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem adjacency_matrix_power_counts_walks_7a {α V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [DecidableEq V] [Semiring α]
    (n : ℕ) (u v : V) : (G.adjMatrix α ^ n) u v = Fintype.card {p : G.Walk u v | p.length = n} := by sorry

end FamousTheorems
