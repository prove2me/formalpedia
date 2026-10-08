-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_exists_assignment
-- name    : ChinesePostman.Mixed.exists_assignment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:52:11.485848+00:00
-- url     : https://prove2.me/theorems/9dd803c5-9c80-4635-afb7-603e94abdd5e
-- title:
--   §6, p. 118 — directions can be assigned to undirected edges so that the graph stays symmetric, the directed edges span and connect, and the rest stays even
-- statement:
--   Let $G$ be a connected, even, symmetric mixed graph. Then directions can be **assigned** to some of its undirected edges so that the resulting mixed graph $G'$, with the same edges and the same ends and with every directed edge of $G$ keeping its direction, satisfies:
--
--   1. $G'$ is symmetric (considering both directed and assigned edges);
--   2. the directed edges of $G'$ form a connected spanning subgraph of $G$;
--   3. the undirected (unassigned) edges of $G'$ have even degree at every node.
--
--   $$
--   G \text{ connected, even, symmetric} \;\Longrightarrow\; \exists\, G' \text{ as above.}
--   $$
--
--   This is the outcome of the paper's assignment algorithm (Steps 0–3, pp. 117–118); $G'$ then satisfies the hypotheses of the Rule, so the Rule traces out an Euler tour of $G'$, which is an Euler tour of $G$.
--
--   **Formalization Note** $G'$ is a mixed graph on the same edge type; for each edge the unordered pair of ends is unchanged, and every directed edge of $G$ is directed in $G'$ with the same tail and head. An undirected edge of $G$ may become directed in $G'$ (assigned) in either direction, or stay undirected. The paper's "spanning subgraph" is stated as connectivity through directed edges, which is what the Rule uses.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 118, §6 ('At termination, every node is still symmetric …'; Steps 0–3 on pp. 117–118)

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, p. 118, the outcome of the assignment algorithm: a connected, even, symmetric mixed graph
`G` admits an assignment of directions to some of its undirected edges, giving a mixed graph `G'`
with the same edges and ends in which every directed edge of `G` keeps its direction, such that
`G'` is symmetric, its directed edges form a connected spanning subgraph, and its undirected edges
have even degree at every node. -/
theorem exists_assignment {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) :
    ∃ G' : MixedGraph V E,
      (∀ e, s(G'.tail e, G'.head e) = s(G.tail e, G.head e)) ∧
      (∀ e, G.directed e = true →
        G'.directed e = true ∧ G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
      G'.IsSymmetric ∧ G'.DirectedConnected ∧ (∀ n, Even (G'.undirDeg n)) := by sorry

end ChinesePostman.Mixed
