-- Prove2me | Theorems.Thm_CClosedGraphs_Peeling_types_one_two_le
-- name    : CClosedGraphs.Peeling.types_one_two_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:49.328066+00:00
-- url     : https://prove2.me/theorems/eb533007-7903-4ece-9991-6df791210b89
-- title:
--   §2.1, p. 6 — maximal cliques of types 1 and 2 number at most those of G \ {v}
-- statement:
--   Let $G$ be a finite simple graph, $W$ a set of vertices and $v\in W$. Call a maximal clique $K$ of $G[W]$ of *type 1* if $v\notin K$, and of *type 2* if $v\in K$ and $K\setminus\{v\}$ is a maximal clique of $G[W\setminus\{v\}]$. Then
--   $$\#\{K : K \text{ a maximal clique of } G[W] \text{ of type 1 or 2}\}\ \le\ \mathrm{mc}(G[W\setminus\{v\}]).$$
--
--   In the paper ($W=V$, $G\setminus\{v\}=G[V\setminus\{v\}]$) this is the step "the number of maximal cliques of types 1 and 2 combined is at most $F(n-1,c)$" of the peeling argument. It holds for every graph; no closure hypothesis is involved.
--
--   **Formalization Note** The induced subgraph $G\setminus\{v\}$ of the current graph $G[W]$ is $G[W\setminus\{v\}]$; the right-hand side is the actual number of maximal cliques of that graph, which is at most the paper's $F(|W|-1,c)$ when $G[W]$ is $c$-closed.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 6, §2.1, proof of Theorem 2.1 (types 1–3 and the bound on types 1 and 2)

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Peeling
open Classical in
theorem types_one_two_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) :
    ((maxCliquesIn G W).filter
        (fun K => v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v}))).card
      ≤ numMaxCliquesIn G (W \ {v}) := by sorry
end CClosedGraphs.Peeling
