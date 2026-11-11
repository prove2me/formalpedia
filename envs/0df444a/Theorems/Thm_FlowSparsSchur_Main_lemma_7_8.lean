-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_7_8
-- name    : FlowSparsSchur.Main.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:43.995538+00:00
-- url     : https://prove2.me/theorems/3593b274-fc27-490d-a663-edf9d7cdbda1
-- title:
--   Lemma 7.8 — every row of the entrywise-absolute reverse map Π̄_{H̃→G} has squared ℓ2 norm at most ξ
-- statement:
--   In the setting of Lemma 7.7: let $G$ be a connected graph with conductances on $\{0,\dots,n-1\}$ without self-loops, $S\subseteq V(G)$ with $|S|\ge2$, and $\widetilde H$ a $\xi$-approximate Schur complement of $G$ onto $S$, i.e. a graph on $S$ (no self-loops, conductances $>0$) with $\xi^{-1}L_{\mathrm{Schur}(G,S)}\preceq L_{\widetilde H}\preceq\xi L_{\mathrm{Schur}(G,S)}$. For §7's map
--   $$\Pi_{\widetilde H\to G}=C_G^{1/2}B_GL_G^\dagger P_{\widetilde H\to V(G)}B_{\widetilde H}^\top C_{\widetilde H}^{1/2},$$
--   every edge $e\in E(G)$ satisfies
--   $$\big\|\overline\Pi_{\widetilde H\to G}(e,:)\big\|_2^2=\sum_{f\in E(\widetilde H)}\big|\Pi_{\widetilde H\to G}(e,f)\big|^2\le\xi .$$
--
--   Differences from the source:
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 26, Lemma 7.8 (setting of Lemma 7.7)

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Lemma 7.8** (p. 26), in the setting of Lemma 7.7. Let `G` be a connected graph with
conductances on `{0, …, n − 1}` (no self-loops), `S ⊆ V(G)` with `|S| ≥ 2`, and `H̃` a
`ξ`-approximate Schur complement of `G` onto `S` (a graph on `S`, no self-loops, conductances `> 0`,
`ξ⁻¹ L_{Schur(G,S)} ⪯ L_H̃ ⪯ ξ L_{Schur(G,S)}`). For §7's
`Π_{H̃→G} = C_G^{1/2} B_G L_G^† P_{H̃→V(G)} B_H̃ᵀ C_H̃^{1/2}`, every row of its entrywise absolute
value has squared `ℓ₂` norm at most `ξ`. -/
theorem lemma_7_8 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ : ℝ) (hG : G.IsCondGraph) (hS : 2 ≤ S.card)
    (hHt : Ht.NoLoops ∧ Ht.PosCond) (happrox : SpecApprox ξ Ht.lap (schurLap G S)) :
    ∀ e : Fin m, ∑ f, (absM (piRevSec7 S G Ht) e f) ^ 2 ≤ ξ := by sorry

end FlowSparsSchur.Main
