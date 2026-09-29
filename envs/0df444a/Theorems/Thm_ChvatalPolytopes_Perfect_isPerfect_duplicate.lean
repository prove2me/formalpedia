-- Prove2me | Theorems.Thm_ChvatalPolytopes_Perfect_isPerfect_duplicate
-- name    : ChvatalPolytopes.Perfect.isPerfect_duplicate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:14:32.207618+00:00
-- url     : https://prove2.me/theorems/a55643e9-1faa-462f-ac85-4992f38276f2
-- title:
--   Lovász's second theorem — duplicating a vertex preserves perfection
-- statement:
--   Let $G=(V,E)$ be a finite perfect graph (in the $\alpha$-perfect sense of the definition of perfection above) and $u\in V$. Let $G'$ be obtained from $G$ by duplicating $u$: add a new vertex $u'$ adjacent to all neighbours of $u$ but not to $u$. Then
--   $$G' \text{ is perfect.}$$
--
--   This theorem of Lovász, cited in §3 of the paper, is applied repeatedly in the implication (ii) $\Rightarrow$ (iii) of the proof of Theorem 3.1, where every vertex $u$ is multiplied by a positive integer $c_u$.
--
--   **Formalization Note** The duplicated graph is the mission's `duplicate G u` on the vertex type `Option V`, with `none` the new vertex.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 140, §3 (Lovász [16, 15], second theorem)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect
import Definitions.Def_ChvatalPolytopes_Perfect_duplicate

namespace ChvatalPolytopes.Perfect

/-- **Lovász's second theorem** (cited in Chvátal 1975, §3, p. 140, from Lovász [16, 15]): a
perfect graph remains perfect after the duplication of an arbitrary vertex `u` (adding a new
vertex `u'` joined to all the neighbours of `u` but not to `u`). "Perfect" is the paper's
α-perfection `IsPerfect`. -/
theorem isPerfect_duplicate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) (u : V) :
    IsPerfect (duplicate G u) := by sorry

end ChvatalPolytopes.Perfect
