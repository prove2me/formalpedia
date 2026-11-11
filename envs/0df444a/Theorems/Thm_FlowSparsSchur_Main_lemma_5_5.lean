-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_5_5
-- name    : FlowSparsSchur.Main.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:48.088224+00:00
-- url     : https://prove2.me/theorems/11b5b7bb-2f79-48e6-9a05-1b72b53999e3
-- title:
--   Lemma 5.5 — average reverse congestion at most q gives H_λ ↪^q G
-- statement:
--   Let $G$ be a connected capacitated graph with conductances on $\{0,\dots,n-1\}$ and $H_1,\dots,H_T$ connected capacitated graphs with conductances on $S\subseteq V(G)$, $|S|\ge2$ (no self-loops, positive capacities and conductances). Let $E_i\in\mathbb R^{E(G)\times E(H_i)}$ be any matrices with
--   $$B_G^\top E_i=P_{H_i\to V(G)}B_{H_i}^\top U_i ,$$
--   and $\mathrm{cong}_{H_i\to G}=U_G^{-1}\overline{E_i}\mathbf 1$. If $\lambda\in\Delta^T$ and $q\in\mathbb R$ satisfy $\sum_i\lambda_i\,\mathrm{cong}_{H_i\to G}(e)\le q$ for every $e\in E(G)$, then
--   $$H_\lambda=\sum_i\lambda_iH_i\overset{q}{\hookrightarrow}G .$$
--
--   Differences from the source:
--   - encoding: H_λ with common edges merged → every edge of every H_i kept as a separate parallel edge of capacity λ_i u_i(e); reason: parallel capacities add, so routability with any congestion is the same in both graphs.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 18, Lemma 5.5

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

open Matrix

/-- **Lemma 5.5** (p. 18). Let `G` be a connected capacitated graph with conductances on
`{0, …, n − 1}` and `H_1, …, H_T` connected capacitated graphs with conductances on a terminal set
`S` (`|S| ≥ 2`). Let `E_i ∈ ℝ^{E(G) × E(H_i)}` be reverse embeddings with
`B_Gᵀ E_i = P_{H_i→V(G)} B_{H_i}ᵀ U_i`, and `cong_i = U_G⁻¹ Ē_i 1`. If `λ ∈ Δ^T` satisfies
`Σ_i λ_i cong_i(e) ≤ q` for all `e ∈ E(G)`, then `H_λ = Σ_i λ_i H_i ↪^q G`. -/
theorem lemma_5_5 {n m T : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    {r : Fin T → ℕ} (H : ∀ i, CGraph S (Fin (r i))) (hS : 2 ≤ S.card)
    (hG : G.IsCapCondGraph) (hH : ∀ i, (H i).IsCapCondGraph)
    (lam : Fin T → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (Emb : ∀ i, Matrix (Fin m) (Fin (r i)) ℝ)
    (hEmb : ∀ i, (G.incidence)ᵀ * Emb i = padOf S * ((H i).incidence)ᵀ * (H i).capMat)
    (q : ℝ) (hq : ∀ e, ∑ i, lam i * congOf G (Emb i) e ≤ q) :
    QEmbeds q (CGraph.combo lam H) G (fun s : S => s) (fun s : S => s.val) := by sorry

end FlowSparsSchur.Main
