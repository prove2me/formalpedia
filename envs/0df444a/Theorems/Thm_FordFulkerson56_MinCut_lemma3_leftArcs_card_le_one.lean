-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_lemma3_leftArcs_card_le_one
-- name    : FordFulkerson56.MinCut.lemma3_leftArcs_card_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:13:02.302991+00:00
-- url     : https://prove2.me/theorems/6199ca85-4cde-4e44-856b-d5901ce5016a
-- title:
--   Lemma 3, p. 401 — no positive chain flow of a maximal flow contains two left arcs
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities, and let $L$ be the set of left arcs. If $f$ is a maximal flow and $C$ is a chain with $f(C)>0$, then $C$ contains at most one arc of $L$:
--   $$|C\cap L|\le 1.$$
--
--   Since every arc of $L$ is saturated by every maximal flow, summing the capacities of the arcs of $L$ counts each positive chain flow of a maximal flow at most once; this gives $v(L)\le$ the maximal flow value.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 401, Lemma 3 (proof continued on p. 402)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem lemma3_leftArcs_card_le_one {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∀ f, IsMaxFlow N f → ∀ C : Finset E, 0 < f C → (C ∩ leftArcs N).card ≤ 1 := by sorry

end FordFulkerson56.MinCut
