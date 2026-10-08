-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_mixed_euler_tour
-- name    : ChinesePostman.Mixed.mixed_euler_tour
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:52:09.771094+00:00
-- url     : https://prove2.me/theorems/15ad3fc5-791a-4642-93d3-ded0e94b4613
-- title:
--   §6, pp. 115–118 — every connected, even, symmetric mixed graph has an Euler tour
-- statement:
--   Let $G$ be a finite mixed graph (some edges directed, some undirected; parallel edges allowed; no loops) that is
--
--   1. **connected** when the directions on the edges are ignored;
--   2. **even**: every node meets an even number of edges, regardless of direction;
--   3. **symmetric**: every node has as many edges directed away from it as directed toward it.
--
--   Then for every node $r$ there is an Euler tour of $G$ starting and ending at $r$:
--
--   $$
--   \exists\,(r = n_1, e_1, n_2, \dots, e_l, n_{l+1} = r) \text{ using every edge exactly once, each directed edge from its tail to its head.}
--   $$
--
--   This is the main result of §6: the paper's algorithm first assigns directions to enough undirected edges and then traces the tour by its Rule. For graphs with only undirected edges it gives Euler's theorem for connected even multigraphs; for graphs with only directed edges, the classical theorem for connected balanced digraphs.
--
--   **Formalization Note** The tour must respect directions: a tour of the underlying undirected multigraph is not enough. The single-node graph without edges is allowed, and its one-node tour is the Euler tour.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 115–118, §6 (announced p. 115, concluded p. 118: 'Thus, the rule previously given will now enable one to actually trace out an Euler tour')

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, pp. 115–118: every connected, even, symmetric mixed graph has an Euler tour, starting at
any prescribed node `r`, that traverses every directed edge in its direction. -/
theorem mixed_euler_tour {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) (r : V) :
    ∃ ns es, G.IsMixedEulerTour ns es ∧ ns.head? = some r := by sorry

end ChinesePostman.Mixed
