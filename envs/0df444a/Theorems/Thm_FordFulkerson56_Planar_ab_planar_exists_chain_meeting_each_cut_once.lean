-- Prove2me | Theorems.Thm_FordFulkerson56_Planar_ab_planar_exists_chain_meeting_each_cut_once
-- name    : FordFulkerson56.Planar.ab_planar_exists_chain_meeting_each_cut_once
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:41:56.870383+00:00
-- url     : https://prove2.me/theorems/170c2227-81dd-40b1-8cc4-7785ff0377c2
-- title:
--   Theorem 2, p. 403 — in an ab-planar network some chain joining a and b meets each cut precisely once
-- statement:
--   Let $N$ be a network with source $a$ and sink $b$ such that
--
--   1. no arc of $N$ joins $a$ and $b$;
--   2. some chain joins $a$ and $b$;
--   3. $N$ is ab-planar: the graph of $N$ together with an additional arc $ab$ can be drawn in the plane without crossings.
--
--   Then there exists a chain $T$ joining $a$ and $b$ which meets each cut of $N$ precisely once:
--   $$\exists\,T \text{ a chain joining } a \text{ and } b\ \text{ such that }\ |T\cap D| = 1\ \text{ for every cut } D \text{ of } N.$$
--
--   Combined with the minimal cut theorem, this gives Ford and Fulkerson's computing procedure for planar networks: load such a chain to its bottleneck capacity, which reduces the value of every cut by the same amount, delete the saturated arcs, and repeat.
--
--   **Formalization Note** Hypothesis 1 is the standing assumption of §2 ("For convenience, we suppose there is no arc in G joining a and b", p. 403). Hypothesis 2 is not on the page; the paper's proof starts from "the chain joining a and b which is top-most", which presupposes one. Without it the statement is false: if $a$ and $b$ lie in different components, the empty set is a cut and no chain joins $a$ and $b$. "Precisely once" is encoded as the intersection having exactly one arc. Planarity is `Nonempty (ABPlaneDrawing N)`.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 403, Theorem 2; standing assumption of §2, p. 403

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_Planar_ABPlaneDrawing

namespace FordFulkerson56.Planar

/-- Theorem 2, p. 403: if `N` is ab-planar (and, as §2 supposes, no arc joins `a` and `b`), there
exists a chain joining `a` and `b` which meets each cut of `N` precisely once. The hypothesis `hconn`
(some chain joins `a` and `b`) is presupposed by the paper's proof and added here. -/
theorem ab_planar_exists_chain_meeting_each_cut_once {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E)
    (hno_ab : ∀ e : E, ¬ ((N.tail e = N.source ∧ N.head e = N.sink) ∨
      (N.tail e = N.sink ∧ N.head e = N.source)))
    (hconn : ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C)
    (hplanar : Nonempty (ABPlaneDrawing N)) :
    ∃ T : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink T ∧
      ∀ D : Finset E, FordFulkerson56.MinCut.IsCut N D → (T ∩ D).card = 1 := by sorry

end FordFulkerson56.Planar
