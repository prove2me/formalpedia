-- Prove2me | Theorems.Thm_CClosedGraphs_Peeling_moon_moser
-- name    : CClosedGraphs.Peeling.moon_moser
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:21.12158+00:00
-- url     : https://prove2.me/theorems/a075d2b3-bc9f-4815-9653-18fb3ffdfe99
-- title:
--   §2.1, p. 7 (cites [45]) — any k-vertex graph has at most 3^{k/3} maximal cliques
-- statement:
--   Let $G$ be a finite simple graph and $W$ a set of $k$ of its vertices. The induced subgraph $G[W]$ has at most $3^{k/3}$ maximal cliques:
--   $$\mathrm{mc}(G[W])\ \le\ 3^{|W|/3}.$$
--
--   This is the bound of Moon and Moser (1965) on the number of maximal cliques of a $k$-vertex graph, in the form used on p. 7 of the paper, where it is applied to the induced subgraphs $G[N(u)\cap N(v)]$ of fewer than $c$ vertices. Taking $W$ to be all vertices gives the bound $3^{|V|/3}$ for $G$ itself.
--
--   **Formalization Note** Stated for induced subgraphs $G[W]$ (the relative form the proof applies); the exponent $|W|/3$ is a real number and the power is the real power. The sharp Moon–Moser values are not claimed.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 7, §2.1, proof of Theorem 2.1 (citing Moon and Moser [45])

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Peeling
theorem moon_moser {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by sorry
end CClosedGraphs.Peeling
