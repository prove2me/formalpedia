-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_flow_value_le_cutValue
-- name    : FordFulkerson56.MinCut.flow_value_le_cutValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:51:08.553278+00:00
-- url     : https://prove2.me/theorems/177ef9af-4ef9-4568-bd51-ebccc7f0e246
-- title:
--   Proof of Theorem 1, p. 402 — the value of every flow is at most v(D) for every disconnecting set D
-- statement:
--   Let $N$ be a finite network with source $a$, sink $b$ and positive capacities. For every flow $f$ and every disconnecting set $D$,
--   $$\mathrm{val}(f)\le v(D)=\sum_{e\in D}c(e).$$
--
--   This is the easy half of the minimal cut theorem (weak duality): each chain flow passes through some arc of $D$.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 402, proof of Theorem 1, final paragraph, first clause

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

namespace FordFulkerson56.MinCut

theorem flow_value_le_cutValue {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∀ f, IsFlow N f → ∀ D : Finset E, IsDisconnecting N D → value f ≤ cutValue N D := by sorry

end FordFulkerson56.MinCut
