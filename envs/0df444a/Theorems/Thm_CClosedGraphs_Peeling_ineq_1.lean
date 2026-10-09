-- Prove2me | Theorems.Thm_CClosedGraphs_Peeling_ineq_1
-- name    : CClosedGraphs.Peeling.ineq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:24.472309+00:00
-- url     : https://prove2.me/theorems/215a40ba-b8ac-48e4-b7d6-5151b84da67b
-- title:
--   §2.1, p. 7, (1) — type-3 cliques number at most Σ_u F(|N(u) ∩ N(v)|, c)
-- statement:
--   Let $G$ be a finite simple graph, $W$ a set of vertices and $v\in W$. The number of maximal cliques $K$ of $G[W]$ of type 3 ($v\in K$ and $K\setminus\{v\}$ not maximal in $G[W\setminus\{v\}]$) satisfies
--   $$\#\{\text{type-3 maximal cliques of } G[W]\}\ \le\ \sum_{u\in W\setminus(N(v)\cup\{v\})} \mathrm{mc}\big(G[W\cap N(u)\cap N(v)]\big).$$
--
--   This is inequality (1) of the paper, with each $F(|N(u)\cap N(v)|,c)$ replaced by the actual number of maximal cliques of $G[N(u)\cap N(v)]$, which is at most $F(|N(u)\cap N(v)|,c)$ since induced subgraphs of a $c$-closed graph are $c$-closed. Combined with the Moon–Moser bound it gives the $3^{(c-1)/3}n$ term of the recursion.
--
--   **Formalization Note** The sum runs over the finite set of $u\in W$ with $u\neq v$ and $u$ not adjacent to $v$; neighbourhoods are taken in $G[W]$.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 7, §2.1, display (1)

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Peeling
open Classical in
theorem ineq_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) :
    ((maxCliquesIn G W).filter
        (fun K => v ∈ K ∧ K.erase v ∉ maxCliquesIn G (W \ {v}))).card
      ≤ ∑ u ∈ W.toFinset.filter (fun u => u ≠ v ∧ ¬ G.Adj v u),
          numMaxCliquesIn G (W ∩ G.commonNeighbors v u) := by sorry
end CClosedGraphs.Peeling
