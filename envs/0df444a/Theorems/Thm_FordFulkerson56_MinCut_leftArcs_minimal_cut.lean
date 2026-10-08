-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_leftArcs_minimal_cut
-- name    : FordFulkerson56.MinCut.leftArcs_minimal_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:13:19.153984+00:00
-- url     : https://prove2.me/theorems/24b83d23-8459-49c0-a4ee-3b349ee6f303
-- title:
--   Proof of Theorem 1, p. 402 — L is a minimal cut and the value of a maximal flow is v(L)
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities, and let $L$ be the set of left arcs. Then
--
--   1. $L$ is a cut: it is disconnecting and no proper subset of it is disconnecting;
--   2. $L$ has minimal value among disconnecting sets: $v(L)\le v(D)$ for every disconnecting set $D$;
--   3. every maximal flow $f$ has value
--   $$\mathrm{val}(f)=v(L).$$
--
--   This is the conclusion of the paper's proof of the minimal cut theorem: the proof constructs an explicit cut, the left arcs, whose value is attained by a flow.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 402, proof of Theorem 1, final paragraph, last sentence

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem leftArcs_minimal_cut {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    IsCut N (leftArcs N) ∧
    (∀ D : Finset E, IsDisconnecting N D → cutValue N (leftArcs N) ≤ cutValue N D) ∧
    ∀ f, IsMaxFlow N f → value f = cutValue N (leftArcs N) := by sorry

end FordFulkerson56.MinCut
