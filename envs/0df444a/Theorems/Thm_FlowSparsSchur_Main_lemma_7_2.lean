-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_7_2
-- name    : FlowSparsSchur.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:53.25731+00:00
-- url     : https://prove2.me/theorems/5fd83481-b5a2-4af5-9f4f-758449c92d55
-- title:
--   Lemma 7.2 — average-congestion bound ⟨p, cong_{H̃(ν)→G}⟩ ≤ α_avg = 2Λ_fΛ_r
-- statement:
--   Let $G$ be a connected capacitated graph on $\{0,\dots,n-1\}$ (no self-loops, $m$ edges, capacities $u>0$), $S\subseteq V(G)$ with $k=|S|\ge2$, and $p\in\Delta^m$. Let $G_c$ be $G$ with conductances
--   $$c_e=\frac{u_e^2}{p_e+1/m},$$
--   and let $\widetilde H$ be a graph on $S$ (no self-loops, conductances $>0$) that $\xi$-spectrally approximates $\mathrm{Schur}(G_c,S)$. Let $\Lambda_f=C_f\sqrt\xi\log^{3/2}k$ and $\Lambda_r=C_r\sqrt\xi\log k$, where $C_f,C_r$ are the constants of Theorem 9.1: the hypotheses are Theorem 9.1's two bounds $\|\overline\Pi_{G_c\to\widetilde H}\|_2\le\Lambda_f$ and $\|\overline\Pi_{\widetilde H\to G_c}\|_2\le\Lambda_r$ for this instance. With $\nu=\nu(G_c\to\widetilde H)$ the dominating capacities,
--   $$\big\langle p,\ \mathrm{cong}_{\widetilde H(\nu)\to G_c}\big\rangle\le\alpha_{\mathrm{avg}}=2\Lambda_f\Lambda_r .$$
--
--   This is the oracle guarantee of the multiplicative-weights scheme of Algorithm 1.
--
--   Differences from the source:
--   - reading: Λ_f = O(√ξ log^{1.5}k), Λ_r = O(√ξ log k) "with constants from Theorem 9.1" → Λ_f = C_f√ξ ln^{3/2}k, Λ_r = C_r√ξ ln k for any reals C_f, C_r for which Theorem 9.1's two bounds hold; reason: the source defines the constants as those of Theorem 9.1 (a separate milestone), so the lemma is stated relative to them.
--   - generalization: Theorem 9.1's bounds for every instance → only for the instance (G_c, S, H̃) at hand; reason: the proof uses Theorem 9.1 only there, and with Theorem 9.1's universal constants the hypothesis holds, giving the source's lemma.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 23, Lemma 7.2

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Lemma 7.2** (p. 23). Let `G` be a connected capacitated graph on `{0, …, n − 1}` (no self-loops,
`m` edges, capacities `u > 0`), `S ⊆ V(G)` with `k = |S| ≥ 2`, `p ∈ Δ^m`, and `G_c` the graph `G`
with conductances `c_e = u_e² / (p_e + 1/m)`. Let `H̃` be a graph on `S` (no self-loops, conductances
`> 0`) that `ξ`-spectrally approximates `Schur(G_c, S)`. Let `Λ_f = C_f √ξ log^{3/2} k` and
`Λ_r = C_r √ξ log k`, where `C_f, C_r` are constants for which Theorem 9.1's bounds
`‖Π̄_{G_c→H̃}‖₂ ≤ Λ_f`, `‖Π̄_{H̃→G_c}‖₂ ≤ Λ_r` hold (here assumed only for this instance). Then, with
`ν = ν(G_c → H̃)` the dominating capacities, `⟨p, cong_{H̃(ν)→G_c}⟩ ≤ α_avg = 2 Λ_f Λ_r`. -/
theorem lemma_7_2 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ Cf Cr : ℝ) (p : Fin m → ℝ)
    (hG : G.NoLoops ∧ G.PosCap ∧ G.Connected) (hS : 2 ≤ S.card)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∑ e, p e = 1)
    (hHt : Ht.NoLoops ∧ Ht.PosCond)
    (happrox : SpecApprox ξ Ht.lap
      (schurLap (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) S))
    (hf : OpNormLe (absM (piFwd S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht))
      (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)))
    (hr : OpNormLe (absM (piRev S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht))
      (Cr * Real.sqrt ξ * Real.log (S.card : ℝ))) :
    ∑ e, p e * revCong S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ)))
        (Ht.withCap (domCap S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht)) e
      ≤ 2 * (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)) *
        (Cr * Real.sqrt ξ * Real.log (S.card : ℝ)) := by sorry

end FlowSparsSchur.Main
