-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_5_3
-- name    : FlowSparsSchur.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:57.766938+00:00
-- url     : https://prove2.me/theorems/ff42c1c4-efbd-4da8-ae04-b803c0351f9b
-- title:
--   Lemma 5.3 — H q-embeds into G with q = ‖cong_{H→G}‖_∞
-- statement:
--   Let $G$ be a connected capacitated graph with conductances on $\{0,\dots,n-1\}$ and $H$ a connected capacitated graph with conductances on $S\subseteq V(G)$, $|S|\ge2$ (no self-loops, positive capacities and conductances). With the reverse electrical embedding $E_{H\to G}=C_GB_GL_G^\dagger P_{H\to V(G)}B_H^\top U_H$ and its congestion $\mathrm{cong}_{H\to G}=U_G^{-1}\overline E_{H\to G}\mathbf 1$,
--   $$H\overset{q}{\hookrightarrow}G\qquad\text{with } q=\|\mathrm{cong}_{H\to G}\|_\infty=\max_{e\in E(G)}\mathrm{cong}_{H\to G}(e).$$
--
--   This is the reverse half of the flow-sparsifier guarantee.
--
--   Differences from the source:
--   - encoding: ‖cong_{H→G}‖_∞ → the supremum ⨆_e cong_{H→G}(e) over the finitely many edges; reason: the congestion is nonnegative and E(G) is nonempty (G is connected with at least two vertices), so the supremum is the maximum, which is the ∞-norm.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 18, Lemma 5.3

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Lemma 5.3** (p. 18). For connected capacitated graphs with conductances `G` on
`{0, …, n − 1}` and `H` on a terminal set `S` (`|S| ≥ 2`), `H ↪^q G` with
`q = ‖cong_{H→G}‖_∞ = max_e cong_{H→G}(e)`, `cong_{H→G} = U_G⁻¹ Ē_{H→G} 1`. -/
theorem lemma_5_3 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (H : CGraph S (Fin r)) (hS : 2 ≤ S.card) (hG : G.IsCapCondGraph) (hH : H.IsCapCondGraph) :
    QEmbeds (⨆ e, revCong S G H e) H G (fun s : S => s) (fun s : S => s.val) := by sorry

end FlowSparsSchur.Main
