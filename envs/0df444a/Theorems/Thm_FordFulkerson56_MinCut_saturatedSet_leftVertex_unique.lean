-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_saturatedSet_leftVertex_unique
-- name    : FordFulkerson56.MinCut.saturatedSet_leftVertex_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:12:48.853121+00:00
-- url     : https://prove2.me/theorems/466dc0f2-c60f-4e5e-92a5-499b81a05df4
-- title:
--   Proof of Theorem 1, pp. 400–401 — maximal flows orient every arc of S the same way
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities, and let $S$ be the set of arcs saturated in every maximal flow. For an arc $\alpha\in S$, say that a vertex $v$ is a left vertex of $\alpha$ if some positive chain flow of some maximal flow, traversed from $a$ to $b$, passes through $\alpha$ entering it at $v$. Then every arc of $S$ has at most one left vertex:
--   $$\alpha\in S,\ v \text{ and } w \text{ left vertices of } \alpha\ \Longrightarrow\ v=w.$$
--   The two witnesses may come from two different maximal flows.
--
--   In the paper's words, the arcs of $S$ have a definite orientation assigned to them by maximal flows. This is what makes "the left vertex of $\alpha$" well defined, and hence the set $L$ of left arcs.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), pp. 400–401, proof of Theorem 1, paragraph after the proof of Lemma 1

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem saturatedSet_leftVertex_unique {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∀ e ∈ saturatedSet N, ∀ v w : V, IsLeftVertex N e v → IsLeftVertex N e w → v = w := by sorry

end FordFulkerson56.MinCut
