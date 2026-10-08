-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_maximal_arborescence_spanning
-- name    : ChinesePostman.Mixed.maximal_arborescence_spanning
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:52:08.772211+00:00
-- url     : https://prove2.me/theorems/12af71f8-452e-419b-8980-41d175b57221
-- title:
--   §6, pp. 115–116 — a maximal arborescence of directed edges is spanning when the directed edges form a symmetric connected spanning subgraph
-- statement:
--   Let $G$ be a mixed graph whose directed edges form a symmetric, connected spanning subgraph: $G$ is symmetric, and every two nodes are joined by a walk, directions ignored, that uses only directed edges. Let $T$ be an arborescence with root $r$ on a node set $W$, made of directed edges, and suppose $T$ is **maximal**: no directed edge is directed toward a node of $W$ and away from a node not in $W$. Then $T$ is spanning:
--
--   $$
--   W = N .
--   $$
--
--   Applied to a graph whose edges are all directed, this is the paper's statement that a maximal arborescence of a symmetric, connected, directed graph is spanning; the paper then notes that it remains true in the mixed graphs just described. It provides the spanning arborescence the Rule starts from.
--
--   **Formalization Note** Maximality is stated as the closure condition on the node set $W$, which is exactly the paper's stopping test for growing the arborescence.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 115–116, §6 (maximal arborescence is spanning; 'In such a graph, a maximal arborescence is still spanning', p. 116)

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, pp. 115–116: if the directed edges of a mixed graph form a symmetric, connected spanning
subgraph, then every maximal arborescence of directed edges is spanning. -/
theorem maximal_arborescence_spanning {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (hconn : G.DirectedConnected)
    (W : Finset V) (r : V) (a : V → Option E) (harb : G.IsArborescence W r a)
    (hmax : G.IsMaximalNodeSet W) :
    W = Finset.univ := by sorry

end ChinesePostman.Mixed
