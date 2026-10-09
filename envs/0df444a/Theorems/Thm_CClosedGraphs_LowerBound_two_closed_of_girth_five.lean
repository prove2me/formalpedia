-- Prove2me | Theorems.Thm_CClosedGraphs_LowerBound_two_closed_of_girth_five
-- name    : CClosedGraphs.LowerBound.two_closed_of_girth_five
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:20.164184+00:00
-- url     : https://prove2.me/theorems/a87f60d0-2c9b-4c26-92cc-0317e9e4da2c
-- title:
--   §1.4, p. 5 — a graph of girth at least 5 is 2-closed, and each of its edges is a maximal clique
-- statement:
--   Let $H$ be a finite graph of girth at least $5$, i.e. without triangles and without $4$-cycles. Then
--
--   1. $H$ is $2$-closed (vacuously: no two distinct vertices have two common neighbours), and
--   2. every edge of $H$ is a maximal clique, so
--   $$
--   |E(H)| \ \le\ \#\mathrm{MC}(H).
--   $$
--
--   The paper makes this observation for the point–line incidence graph of a finite projective plane, which has $\Theta(n^{3/2})$ edges, to show that $2$-closed graphs can have $\Omega(n^{3/2})$ maximal cliques. Combined with a graph of girth at least $5$ and many edges, it gives the lower bound for $c \in \{2, 3\}$.
--
--   **Formalization Note** The page states the observation for the projective-plane incidence graph (girth $6$). The two properties it uses are "no $4$-cycle" ($2$-closed) and "no triangle" (edges are maximal cliques), and girth at least $5$ is exactly both, so the statement is made for every graph of girth at least $5$ (Mathlib's `egirth`, which is $\infty$ for forests).
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 5, §1.4 (projective-plane construction of Eschen, Hoàng, Spinrad and Sritharan [22])

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

namespace CClosedGraphs.LowerBound
theorem two_closed_of_girth_five {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (hH : 5 ≤ H.egirth) : CClosedGraphs.Peeling.IsCClosed 2 H ∧ H.edgeSet.ncard ≤ CClosedGraphs.Peeling.numMaxCliques H := by sorry
end CClosedGraphs.LowerBound
