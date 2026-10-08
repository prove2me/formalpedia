-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_lemma2_leftArcs_disconnecting
-- name    : FordFulkerson56.MinCut.lemma2_leftArcs_disconnecting
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:13:32.914981+00:00
-- url     : https://prove2.me/theorems/3052e344-5477-4b8c-bfb1-2080e2fcdf94
-- title:
--   Lemma 2, p. 401 — the left arcs L form a disconnecting set
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities, and let $L$ be the set of left arcs of $S$: the arcs $\alpha$ saturated by every maximal flow for which some maximal flow $f$ admits a chain (possibly null) from $a$ to the left vertex of $\alpha$ with no arc saturated by $f$. Then $L$ is a disconnecting set:
--   $$\forall\, C \text{ chain joining } a,b:\quad C\cap L\neq\emptyset.$$
--
--   Together with Lemma 3 this shows that $v(L)$ equals the value of a maximal flow.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 401, Lemma 2

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem lemma2_leftArcs_disconnecting {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    IsDisconnecting N (leftArcs N) := by sorry

end FordFulkerson56.MinCut
