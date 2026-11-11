-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_theorem_9_1
-- name    : FlowSparsSchur.Main.theorem_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:44.283599+00:00
-- url     : https://prove2.me/theorems/cabdcebe-7422-488f-a68c-37ee22413b58
-- title:
--   Theorem 9.1 — localization on approximate Schur complements: ‖Π̄_{G→H̃}‖₂ = O(√ξ log^{3/2}|S|), ‖Π̄_{H̃→G}‖₂ = O(√ξ log|S|)
-- statement:
--   There are universal constants $C_f,C_r>0$ such that the following holds. Let $G$ be a connected graph with conductances on $\{0,\dots,n-1\}$ without self-loops, let $S\subseteq V(G)$ with $|S|\ge2$, let $\xi\ge1$, let $H=\mathrm{Schur}(G,S)$, and let $\widetilde H$ be any graph on $S$ (no self-loops, conductances $>0$) with $\xi^{-1}L_H\preceq L_{\widetilde H}\preceq\xi L_H$. With $D_G=C_G^{1/2}B_G$, the Schur projection $P_{G\to S}$, and
--   $$\Pi_{G\to\widetilde H}=D_{\widetilde H}L_{\widetilde H}^\dagger P_{G\to S}D_G^\top,\qquad \Pi_{\widetilde H\to G}=D_GP_{G\to S}^\top L_H^\dagger D_{\widetilde H}^\top ,$$
--   the entrywise absolute values satisfy
--   $$\big\|\overline\Pi_{G\to\widetilde H}\big\|_2\le C_f\sqrt\xi\,\log^{3/2}|S|,\qquad \big\|\overline\Pi_{\widetilde H\to G}\big\|_2\le C_r\sqrt\xi\,\log|S| .$$
--
--   This localization of electrical flows on approximate Schur complements is the paper's main technical contribution; it bounds both the average congestion (Lemma 7.2) and the width (Lemma 7.3) of the multiplicative-weights scheme.
--
--   Differences from the source:
--   - reading: O(√ξ log^{3/2}|S|) and O(√ξ log|S|) → C_f√ξ ln^{3/2}|S| and C_r√ξ ln|S| with C_f, C_r universal; reason: the O(·) of a theorem is a fixed constant, independent of G, S, ξ, H̃.
--   - encoding: ‖A‖₂ ≤ c → ‖Ax‖₂ ≤ c‖x‖₂ for every x; reason: this is the definition of the operator norm bound, written without a supremum.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 28, Theorem 9.1

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Theorem 9.1** (p. 28). There are universal constants `C_f, C_r > 0` such that for every
connected graph `G` with conductances on `{0, …, n − 1}` (no self-loops), every `S ⊆ V(G)` with
`|S| ≥ 2`, every `ξ ≥ 1` and every graph `H̃` on `S` (no self-loops, conductances `> 0`) with
`ξ⁻¹ L_H ⪯ L_H̃ ⪯ ξ L_H`, `H = Schur(G, S)`, the entrywise absolute values of
`Π_{G→H̃} = D_H̃ L_H̃^† P_{G→S} D_Gᵀ` and `Π_{H̃→G} = D_G P_{G→S}ᵀ L_H^† D_H̃ᵀ` satisfy
`‖Π̄_{G→H̃}‖₂ ≤ C_f √ξ log^{3/2}|S|` and `‖Π̄_{H̃→G}‖₂ ≤ C_r √ξ log |S|`. -/
theorem theorem_9_1 :
    ∃ Cf Cr : ℝ, 0 < Cf ∧ 0 < Cr ∧
    ∀ (n m r : ℕ) (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n)) (Ht : CGraph S (Fin r))
      (ξ : ℝ),
      G.IsCondGraph → 2 ≤ S.card → 1 ≤ ξ → Ht.NoLoops → Ht.PosCond →
      SpecApprox ξ Ht.lap (schurLap G S) →
      OpNormLe (absM (piFwd S G Ht)) (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)) ∧
      OpNormLe (absM (piRev S G Ht)) (Cr * Real.sqrt ξ * Real.log (S.card : ℝ)) := by sorry

end FlowSparsSchur.Main
