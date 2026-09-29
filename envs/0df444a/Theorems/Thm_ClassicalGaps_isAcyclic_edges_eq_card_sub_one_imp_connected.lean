-- Prove2me | Theorems.Thm_ClassicalGaps_isAcyclic_edges_eq_card_sub_one_imp_connected
-- name    : ClassicalGaps.isAcyclic_edges_eq_card_sub_one_imp_connected
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T22:23:49.022946+00:00
-- url     : https://prove2.me/theorems/72dec66e-f677-4e54-a0f8-cf0374dacd93
-- title:
--   A forest with |V|-1 edges is connected (spanning tree criterion)
-- statement:
--   For a finite simple graph $G$ on vertex set $V$: if $G$ is acyclic (a forest) and has exactly $|V|-1$ edges, then $G$ is connected (hence a spanning tree). This is the standard graph-theoretic fact that a forest achieves the maximum possible edge count for an acyclic graph on $|V|$ vertices exactly when it is a single tree, used as a lemma in the Kirchhoff matrix-tree theorem decomposition (see `ClassicalGaps.orientedIncMatrix_submatrix_det_eq_spanningTree_indicator`, which needs it to characterize when an edge-subset forms a spanning tree).

import Mathlib

namespace ClassicalGaps

theorem isAcyclic_edges_eq_card_sub_one_imp_connected
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (hcard : Nat.card G.edgeSet + 1 = Nat.card V) :
    G.Connected := by sorry

end ClassicalGaps
