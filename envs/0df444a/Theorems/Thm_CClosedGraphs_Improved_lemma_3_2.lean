-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_lemma_3_2
-- name    : CClosedGraphs.Improved.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:35.052738+00:00
-- url     : https://prove2.me/theorems/ee71d917-2f48-4ed0-b572-d803978ec988
-- title:
--   Lemma 3.2, p. 9 — the neighbourhood of a vertex induces a (c−1)-closed graph
-- statement:
--   Let $c\ge 1$, let $G$ be a graph and $W$ a vertex set such that $G[W]$ is $c$-closed, and let $v\in W$. Then the neighbourhood of $v$ inside $W$ induces a $(c-1)$-closed graph:
--   $$G[W\cap N(v)]\ \text{is $(c-1)$-closed}.$$
--
--   The paper states this for $W=V$ ("For any $v$, $G[N(v)]$ is a $(c-1)$-closed graph"); the relative form is what the induction on induced subgraphs uses. It lowers the closure parameter by one, which drives the induction on $c$ in Theorem 3.1.
--
--   **Formalization Note** $c-1$ is natural-number subtraction, safe because $c\ge1$. For $c=1$ the conclusion says that $W\cap N(v)$ is a clique.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 9, Lemma 3.2

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W) :
    IsCClosedOn (c - 1) G (W ∩ G.neighborSet v) := by sorry
end CClosedGraphs.Improved
