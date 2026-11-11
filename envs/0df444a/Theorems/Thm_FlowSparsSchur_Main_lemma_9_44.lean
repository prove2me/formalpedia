-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_9_44
-- name    : FlowSparsSchur.Main.lemma_9_44
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:40.848301+00:00
-- url     : https://prove2.me/theorems/4b9e7bbb-c6a8-48c9-a02f-92f8a2df2493
-- title:
--   Lemma 9.44 — weighted normalized flows are bounded by potential dissipation
-- statement:
--   Work in the setting of Theorem 9.1: $G$ a connected graph with conductances on $\{0,\dots,n-1\}$ without self-loops, $S\subseteq V(G)$ with $|S|\ge2$, $\xi\ge1$, $H=\mathrm{Schur}(G,S)$, and $\widetilde H$ a graph on $S$ (no self-loops, conductances $>0$) with $\xi^{-1}L_H\preceq L_{\widetilde H}\preceq\xi L_H$. Let $x\in\mathbb R^{E(\widetilde H)}_{\ge0}$ and $y\in\mathbb R^{E(G)}_{\ge0}$ with $\|x\|_2=\|y\|_2=1$, and define
--   $$\alpha(v)=\tfrac12\sum_{e\in E(\widetilde H),\,v\in e}x(e)^2\ (v\in S),\qquad \nu(v)=\tfrac12\sum_{e\in E(G),\,v\in e}y(e)^2\ (v\in V(G)),\qquad \beta=P_{G\to S}\nu .$$
--   Then $\beta\ge0$, $\alpha^\top\mathbf 1=\nu^\top\mathbf 1=\beta^\top\mathbf 1=1$, and for every positive vector $h\in\mathbb R^S_{>0}$, with $g=\mathbf 1+h$ and the potential dissipation $I$,
--   1. $\big(x^\top|D_{\widetilde H}h|\big)^2\le(\alpha^\top h)\,I_{\widetilde H}(h)$,
--   2. $\big(y^\top|D_GP_{G\to S}^\top h|\big)^2\le(\beta^\top g)\,I_H(g)$,
--   3. $\big(x^\top|D_{\widetilde H}h|\big)^2\le4\xi\,(\alpha^\top h)\,I_H(h)$.
--
--   The absolute values are entrywise. These bounds turn the localization norms of Theorem 9.1 into dissipation integrals of the heat flow.
--
--   Differences from the source:
--   - encoding: "for any fixed heat capacity distribution on S, let h_t ∈ ℝ^S_{>0} be a positive vector … for t > 0" → for every positive vector h ∈ ℝ^S_{>0}; reason: h_t is an arbitrary positive vector, the heat capacity and t do not enter the statement.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 48, Lemma 9.44

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding
import Definitions.Def_FlowSparsSchur_Main_Heat

namespace FlowSparsSchur.Main

open Matrix

/-- **Lemma 9.44** (p. 48). In the setting of Theorem 9.1 (a connected graph `G` with conductances on
`{0, …, n − 1}` without self-loops, `S ⊆ V(G)` with `|S| ≥ 2`, `ξ ≥ 1`, `H = Schur(G, S)`, and a graph
`H̃` on `S` without self-loops, conductances `> 0`, `ξ⁻¹ L_H ⪯ L_H̃ ⪯ ξ L_H`), let `x ∈ ℝ^{E(H̃)}_{≥0}`,
`y ∈ ℝ^{E(G)}_{≥0}` with `‖x‖₂ = ‖y‖₂ = 1`, `α(v) = ½ Σ_{e ∋ v} x(e)²` (`v ∈ S`),
`ν(v) = ½ Σ_{e ∋ v} y(e)²` (`v ∈ V(G)`), `β = P_{G→S} ν`. Then `β ≥ 0`, `αᵀ1 = νᵀ1 = βᵀ1 = 1`, and
for every positive vector `h ∈ ℝ^S_{>0}`, with `g = 1 + h`:
1. `(xᵀ |D_H̃ h|)² ≤ (αᵀh) I_H̃(h)`;
2. `(yᵀ |D_G P_{G→S}ᵀ h|)² ≤ (βᵀg) I_H(g)`;
3. `(xᵀ |D_H̃ h|)² ≤ 4ξ (αᵀh) I_H(h)`. -/
theorem lemma_9_44 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ : ℝ) (hG : G.IsCondGraph) (hS : 2 ≤ S.card) (hξ : 1 ≤ ξ)
    (hHt : Ht.NoLoops ∧ Ht.PosCond) (happrox : SpecApprox ξ Ht.lap (schurLap G S))
    (x : Fin r → ℝ) (y : Fin m → ℝ) (hx0 : ∀ f, 0 ≤ x f) (hy0 : ∀ e, 0 ≤ y e)
    (hx1 : norm2 x = 1) (hy1 : norm2 y = 1) :
    (∀ v, 0 ≤ (schurProj G S *ᵥ halfEndpointMass G y) v) ∧
    ∑ v, halfEndpointMass Ht x v = 1 ∧ ∑ v, halfEndpointMass G y v = 1 ∧
    ∑ v, (schurProj G S *ᵥ halfEndpointMass G y) v = 1 ∧
    ∀ h : S → ℝ, (∀ v, 0 < h v) →
      (x ⬝ᵥ (fun f => |(Ht.wInc *ᵥ h) f|)) ^ 2 ≤
          (halfEndpointMass Ht x ⬝ᵥ h) * dissipation Ht.lap h ∧
      (y ⬝ᵥ (fun e => |(G.wInc *ᵥ ((schurProj G S)ᵀ *ᵥ h)) e|)) ^ 2 ≤
          ((schurProj G S *ᵥ halfEndpointMass G y) ⬝ᵥ (fun v => 1 + h v)) *
            dissipation (schurLap G S) (fun v => 1 + h v) ∧
      (x ⬝ᵥ (fun f => |(Ht.wInc *ᵥ h) f|)) ^ 2 ≤
          4 * ξ * (halfEndpointMass Ht x ⬝ᵥ h) * dissipation (schurLap G S) h := by sorry

end FlowSparsSchur.Main
