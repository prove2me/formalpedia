-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_ineq_2
-- name    : CClosedGraphs.Improved.ineq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:18.977176+00:00
-- url     : https://prove2.me/theorems/11f3a180-a1c0-4a12-b6ee-a4f9a625f429
-- title:
--   Inequality (2), p. 9 — |𝒦| ≤ Σ_S F(|N(S) ∩ N₂(v)|, c−1)
-- statement:
--   Let $G$ be any graph, $W$ a vertex set and $v\in W$; neighbourhoods and the second neighbourhood $N_2(v)$ are taken in $G[W]$. Let $\mathcal K$ be the set of maximal cliques of $G[W]$ that do not contain $v$ but contain some neighbour of $v$. Then
--   $$|\mathcal K|\;\le\;\sum_{\emptyset\ne S\subseteq W\cap N(v)} \mathrm{mc}\big(G[N(S)\cap N_2(v)]\big),$$
--   where $N(S)=\bigcap_{u\in S}N(u)$.
--
--   This is inequality (2) of the proof of Theorem 3.1, with $F(|N(S)\cap N_2(v)|,c-1)$ replaced by the actual number of maximal cliques of $G[N(S)\cap N_2(v)]$; the $(c-1)$-closedness of these graphs, which turns the count into $F$, is used in the Case 2 count. It groups the cliques $K\in\mathcal K$ by $S=K\cap N(v)$.
--
--   **Formalization Note** The sum runs over non-empty $S$, as the paper defines $N(S)$ only for non-empty $S$; this makes the bound stronger than a sum over all $S\subseteq N(v)$. No closure hypothesis is needed.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 9, proof of Theorem 3.1, Case 2, inequality (2)

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
open Classical in
theorem ineq_2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      ∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        CClosedGraphs.Peeling.numMaxCliquesIn G (commonNbrs G S ∩ dist2In G W v) := by sorry
end CClosedGraphs.Improved
