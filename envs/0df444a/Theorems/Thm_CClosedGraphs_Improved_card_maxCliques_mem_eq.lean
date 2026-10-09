-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_card_maxCliques_mem_eq
-- name    : CClosedGraphs.Improved.card_maxCliques_mem_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:24.246971+00:00
-- url     : https://prove2.me/theorems/db76ba8d-ee3e-484e-9c0c-74fca1eeef1c
-- title:
--   §3, Case 1, p. 9 — maximal cliques through v correspond to maximal cliques of G[N(v)]
-- statement:
--   Let $G$ be any graph, $W$ a vertex set and $v\in W$. The number of maximal cliques of $G[W]$ that contain $v$ equals the number of maximal cliques of the neighbourhood of $v$ in $G[W]$:
--   $$\#\{K \text{ maximal clique of } G[W] : v\in K\} \;=\; \mathrm{mc}\big(G[W\cap N(v)]\big).$$
--
--   This is the identity behind the Case 1 bound $F(n,c)\le nF(\Delta(G),c-1)$ (sum it over $v$) and behind the bound "$v$ is in at most $F(\Delta(G),c-1)$ maximal cliques" in Case 2. No closure hypothesis is needed. When $v$ has no neighbour in $W$ both sides equal $1$: the clique $\{v\}$ on the left, the empty clique on the right.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 9, proof of Theorem 3.1, Case 1

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
theorem card_maxCliques_mem_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      CClosedGraphs.Peeling.numMaxCliquesIn G (W ∩ G.neighborSet v) := by sorry
end CClosedGraphs.Improved
