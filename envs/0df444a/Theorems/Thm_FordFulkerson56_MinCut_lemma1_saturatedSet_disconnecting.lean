-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_lemma1_saturatedSet_disconnecting
-- name    : FordFulkerson56.MinCut.lemma1_saturatedSet_disconnecting
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:12:39.239123+00:00
-- url     : https://prove2.me/theorems/c2eae50c-9a50-495e-b918-d6fe1c9687ea
-- title:
--   Lemma 1, p. 400 — the arcs saturated in every maximal flow form a disconnecting set
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities, and let $S$ be the set of arcs that are saturated in every maximal flow. Then $S$ is a disconnecting set: every chain joining $a$ and $b$ contains an arc of $S$.
--   $$\forall\, C \text{ chain joining } a,b:\quad C\cap S\neq\emptyset.$$
--
--   This is the first step of the proof of the minimal cut theorem; Lemma 2 refines $S$ to the set $L$ of left arcs.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 400, Lemma 1 (with the definition of S immediately before it)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem lemma1_saturatedSet_disconnecting {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    IsDisconnecting N (saturatedSet N) := by sorry

end FordFulkerson56.MinCut
