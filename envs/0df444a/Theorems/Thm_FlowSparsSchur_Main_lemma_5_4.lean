-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_5_4
-- name    : FlowSparsSchur.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:28.935118+00:00
-- url     : https://prove2.me/theorems/34a88745-eeb2-4c04-8023-788eb64412f3
-- title:
--   Lemma 5.4 — 1-embeddings into every H_i give a 1-embedding into every convex combination H_λ
-- statement:
--   Let $G$ be a connected capacitated graph on $\{0,\dots,n-1\}$ and $H_1,\dots,H_T$ connected capacitated graphs on a terminal set $S\subseteq V(G)$ with $|S|\ge2$ (no self-loops, positive capacities). If $G\overset{1}{\hookrightarrow}H_i$ for every $i$, then for every $\lambda\in\Delta^T$ ($\lambda\ge0$, $\sum_i\lambda_i=1$)
--   $$G\overset{1}{\hookrightarrow}H_\lambda:=\sum_{i=1}^T\lambda_iH_i .$$
--
--   Differences from the source:
--   - encoding: H_λ with common edges merged → H_λ with every edge of every H_i kept as a separate parallel edge of capacity λ_i u_i(e); reason: parallel capacities add, so routability with any congestion is the same in both graphs.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 18, Lemma 5.4

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing

namespace FlowSparsSchur.Main

/-- **Lemma 5.4** (p. 18). Let `G` be a connected capacitated graph on `{0, …, n − 1}` and
`H_1, …, H_T` connected capacitated graphs on a terminal set `S` (`|S| ≥ 2`), none with self-loops.
If `G ↪^1 H_i` for every `i`, then `G ↪^1 H_λ = Σ_i λ_i H_i` for every `λ ∈ Δ^T`. -/
theorem lemma_5_4 {n m T : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    {r : Fin T → ℕ} (H : ∀ i, CGraph S (Fin (r i))) (hS : 2 ≤ S.card)
    (hG : G.NoLoops ∧ G.PosCap ∧ G.Connected)
    (hH : ∀ i, (H i).NoLoops ∧ (H i).PosCap ∧ (H i).Connected)
    (hemb : ∀ i, QEmbeds 1 G (H i) (fun s : S => s.val) (fun s : S => s))
    (lam : Fin T → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) :
    QEmbeds 1 G (CGraph.combo lam H) (fun s : S => s.val) (fun s : S => s) := by sorry

end FlowSparsSchur.Main
