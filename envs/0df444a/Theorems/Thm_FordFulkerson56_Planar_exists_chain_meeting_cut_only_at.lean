-- Prove2me | Theorems.Thm_FordFulkerson56_Planar_exists_chain_meeting_cut_only_at
-- name    : FordFulkerson56.Planar.exists_chain_meeting_cut_only_at
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:26:09.593577+00:00
-- url     : https://prove2.me/theorems/24fdca00-2bb5-4ced-b4d3-9bcf62400e58
-- title:
--   Proof of Theorem 2, p. 403 — for each arc α of a cut D, some chain from a to b meets D in α only
-- statement:
--   Let $N$ be a network with source $a$ and sink $b$, let $D$ be a cut of $N$ (a disconnecting set no proper subset of which is disconnecting), and let $\alpha\in D$. Then there is a chain $C$ joining $a$ and $b$ which meets $D$ in $\alpha$ only:
--   $$C\cap D=\{\alpha\}.$$
--
--   This is the step of the proof of Theorem 2 that uses the minimality of a cut: in that proof it is applied to two arcs $\alpha_1,\alpha_2$ of a cut that lie on the same chain. It holds in every network; no planarity is needed.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 403, proof of Theorem 2, sentences beginning "Since D is a cut"

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

namespace FordFulkerson56.Planar

/-- Proof of Theorem 2, p. 403: since `D` is a cut, for each arc `α ∈ D` there is a chain joining the
source and the sink which meets `D` in `α` only. -/
theorem exists_chain_meeting_cut_only_at {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E) (D : Finset E) (hD : FordFulkerson56.MinCut.IsCut N D) (α : E) (hα : α ∈ D) :
    ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C ∧ C ∩ D = {α} := by sorry

end FordFulkerson56.Planar
