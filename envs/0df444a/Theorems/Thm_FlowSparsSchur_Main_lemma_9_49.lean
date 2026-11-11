-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_9_49
-- name    : FlowSparsSchur.Main.lemma_9_49
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:25:12.53728+00:00
-- url     : https://prove2.me/theorems/84ba19b7-2ae3-4dbb-b6b0-91666a0cd2ba
-- title:
--   Lemma 9.49 — the dissipation on H is at most O(ξ log k) times the dissipation on H̃
-- statement:
--   There is a universal constant $C>0$ such that the following holds. In the setting of Theorem 9.1 ($G$ connected with conductances on $\{0,\dots,n-1\}$ without self-loops, $S\subseteq V(G)$ with $k=|S|\ge2$, $\xi\ge1$, $H=\mathrm{Schur}(G,S)$, $\widetilde H$ a graph on $S$ without self-loops, conductances $>0$, $\xi^{-1}L_H\preceq L_{\widetilde H}\preceq\xi L_H$), let $x,y,\alpha,\beta$ be as in Lemma 9.44 and choose the heat capacity
--   $$\mu=\frac{\alpha+\beta+\mathbf 1/k}{3}.$$
--   Then $\mu^\top\mathbf 1=1$, and for every column $h_t=H_tb_v$ ($v\in S$) of the heat kernel $H_t=e^{-tM^{-1}L_{\widetilde H}}M^{-1}$ of $\widetilde H$ with $M=\mathrm{diag}(\mu)$, every $t>0$ and $g_t=\mathbf 1+h_t$,
--   $$I_H(g_t)\le C\,\xi\log k\; I_{\widetilde H}(h_t).$$
--
--   Differences from the source:
--   - reading: O(ξ log k) → C·ξ·ln k with C universal (independent of G, S, ξ, H̃, x, y, v, t); reason: the O(·) of a lemma is a fixed constant.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 51, Lemma 9.49

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding
import Definitions.Def_FlowSparsSchur_Main_Heat

namespace FlowSparsSchur.Main

open Matrix

/-- **Lemma 9.49** (p. 51). There is a universal constant `C > 0` such that the following holds in
the setting of Theorem 9.1 (a connected graph `G` with conductances on `{0, …, n − 1}` without
self-loops, `S ⊆ V(G)` with `k = |S| ≥ 2`, `ξ ≥ 1`, `H = Schur(G, S)`, a graph `H̃` on `S` without
self-loops, conductances `> 0`, `ξ⁻¹ L_H ⪯ L_H̃ ⪯ ξ L_H`). Let `x, y, α, β` be as in Lemma 9.44 and
`µ = (α + β + 1/k)/3`. Then `µᵀ1 = 1`, and for every column `h_t = H_t b_v` (`v ∈ S`) of the heat
kernel `H_t = e^{−t M⁻¹ L_H̃} M⁻¹` of `H̃` with heat capacity `µ` (`M = diag µ`) and every `t > 0`,
with `g_t = 1 + h_t`, `I_H(g_t) ≤ C ξ log k · I_H̃(h_t)`. -/
theorem lemma_9_49 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n m r : ℕ) (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n)) (Ht : CGraph S (Fin r))
      (ξ : ℝ), G.IsCondGraph → 2 ≤ S.card → 1 ≤ ξ → Ht.NoLoops → Ht.PosCond →
      SpecApprox ξ Ht.lap (schurLap G S) →
    ∀ (x : Fin r → ℝ) (y : Fin m → ℝ), (∀ f, 0 ≤ x f) → (∀ e, 0 ≤ y e) →
      norm2 x = 1 → norm2 y = 1 →
      (∑ v, (halfEndpointMass Ht x v + (schurProj G S *ᵥ halfEndpointMass G y) v +
          1 / (S.card : ℝ)) / 3 = 1) ∧
      ∀ (v : S) (t : ℝ), 0 < t →
        dissipation (schurLap G S) (fun u => 1 + heatColumn Ht.lap
            (fun w => (halfEndpointMass Ht x w + (schurProj G S *ᵥ halfEndpointMass G y) w +
              1 / (S.card : ℝ)) / 3) t v u) ≤
          C * ξ * Real.log (S.card : ℝ) *
            dissipation Ht.lap (heatColumn Ht.lap
              (fun w => (halfEndpointMass Ht x w + (schurProj G S *ᵥ halfEndpointMass G y) w +
                1 / (S.card : ℝ)) / 3) t v) := by sorry

end FlowSparsSchur.Main
