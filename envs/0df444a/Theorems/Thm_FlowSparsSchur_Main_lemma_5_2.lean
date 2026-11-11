-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_5_2
-- name    : FlowSparsSchur.Main.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:48.728873+00:00
-- url     : https://prove2.me/theorems/eec6e39c-ca91-4193-86e6-cbe086b1d0ef
-- title:
--   Lemma 5.2 — G 1-embeds into H with its dominating capacities ν(G → H)
-- statement:
--   Let $G$ be a connected capacitated graph with conductances on $\{0,\dots,n-1\}$ (no self-loops, $u_G,c_G>0$), let $S\subseteq V(G)$ with $|S|\ge2$, and let $H$ be a connected uncapacitated graph on $S$ with conductances $c_H>0$ and no self-loops. With the dominating capacities $\nu=\nu(G\to H)=\overline E_{G\to H}\mathbf 1$ of Definition 5.1,
--   $$G\overset{1}{\hookrightarrow}H_\nu ,$$
--   i.e. every $S$-multicommodity demand that can be routed in $G$ with congestion $1$ can be routed in $H_\nu$ with congestion $1$.
--
--   This is the forward half of the flow-sparsifier guarantee for each graph produced by the algorithm.
--
--   Differences from the source:
--   - encoding: uncapacitated graph H → a graph H whose capacity field is ignored (replaced by ν); reason: H_ν keeps the edges and conductances of H and only the capacities ν are used.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 17, Lemma 5.2

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Lemma 5.2** (p. 17). For a connected capacitated graph `G` with conductances on
`{0, …, n − 1}` and a connected uncapacitated graph `H` with conductances on a terminal set `S`
(`|S| ≥ 2`), `G ↪^1 H_ν` for the dominating capacities `ν = ν(G → H) = Ē_{G→H} 1`. -/
theorem lemma_5_2 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (H : CGraph S (Fin r)) (hS : 2 ≤ S.card) (hG : G.IsCapCondGraph) (hH : H.IsCondGraph) :
    QEmbeds 1 G (H.withCap (domCap S G H)) (fun s : S => s.val) (fun s : S => s) := by sorry

end FlowSparsSchur.Main
