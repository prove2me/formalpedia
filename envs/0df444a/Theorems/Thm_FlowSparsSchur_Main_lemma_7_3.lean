-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_7_3
-- name    : FlowSparsSchur.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:56.509114+00:00
-- url     : https://prove2.me/theorems/beb0ae17-079d-4152-8fde-81e270a288a4
-- title:
--   Lemma 7.3 — width bound ‖cong_{H̃(ν)→G}‖_∞ ≤ ρ = √(2ξm)Λ_f
-- statement:
--   Let $G$ be a connected capacitated graph on $\{0,\dots,n-1\}$ (no self-loops, $m$ edges, capacities $u>0$), $S\subseteq V(G)$ with $k=|S|\ge2$, $p\in\Delta^m$, and $G_c$ the graph $G$ with conductances $c_e=u_e^2/(p_e+1/m)$. Let $\widetilde H$ be a graph on $S$ (no self-loops, conductances $>0$) that $\xi$-spectrally approximates $\mathrm{Schur}(G_c,S)$, and let $\Lambda_f=C_f\sqrt\xi\log^{3/2}k$ where $C_f$ is the constant of Theorem 9.1: the hypothesis is Theorem 9.1's bound $\|\overline\Pi_{G_c\to\widetilde H}\|_2\le\Lambda_f$ for this instance. With $\nu=\nu(G_c\to\widetilde H)$, every edge $e$ satisfies
--   $$\mathrm{cong}_{\widetilde H(\nu)\to G_c}(e)\le\rho=\sqrt{2\xi m}\,\Lambda_f .$$
--
--   This is the width bound that sets the iteration count $T=\lceil\rho\log m/\alpha_{\mathrm{avg}}\rceil$ of Algorithm 1. The source's remark $\rho=\widetilde O(\sqrt m)$ is a comment, not a clause.
--
--   Differences from the source:
--   - reading: Λ_f = O(√ξ log^{1.5}k) "with constants from Theorem 9.1" → Λ_f = C_f√ξ ln^{3/2}k for any real C_f for which Theorem 9.1's forward bound holds; reason: the source defines the constant as that of Theorem 9.1, so the lemma is stated relative to it.
--   - generalization: Theorem 9.1's bound for every instance → only for the instance (G_c, S, H̃) at hand; reason: the proof uses Theorem 9.1 only there; with Theorem 9.1's universal constant the hypothesis holds, giving the source's lemma.
--   - encoding: graphs on abstract vertex and edge sets → vertices {0, …, n − 1}, edges indexed by Fin m (graphs on S: edges indexed by Fin r), each edge with a fixed orientation src → dst; reason: a relabeling of vertices and edges changes no instance, and parallel edges are distinct indices.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 23, Lemma 7.3

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding

namespace FlowSparsSchur.Main

/-- **Lemma 7.3** (p. 23). Let `G` be a connected capacitated graph on `{0, …, n − 1}` (no self-loops,
`m` edges, capacities `u > 0`), `S ⊆ V(G)` with `k = |S| ≥ 2`, `p ∈ Δ^m`, and `G_c` the graph `G`
with conductances `c_e = u_e² / (p_e + 1/m)`. Let `H̃` be a graph on `S` (no self-loops, conductances
`> 0`) that `ξ`-spectrally approximates `Schur(G_c, S)`. Let `Λ_f = C_f √ξ log^{3/2} k`, where `C_f`
is a constant for which Theorem 9.1's bound `‖Π̄_{G_c→H̃}‖₂ ≤ Λ_f` holds (here assumed only for this
instance). Then, with `ν = ν(G_c → H̃)`, every edge has `cong_{H̃(ν)→G_c}(e) ≤ ρ = √(2ξm) Λ_f`. -/
theorem lemma_7_3 {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ Cf : ℝ) (p : Fin m → ℝ)
    (hG : G.NoLoops ∧ G.PosCap ∧ G.Connected) (hS : 2 ≤ S.card)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∑ e, p e = 1)
    (hHt : Ht.NoLoops ∧ Ht.PosCond)
    (happrox : SpecApprox ξ Ht.lap
      (schurLap (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) S))
    (hf : OpNormLe (absM (piFwd S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht))
      (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ))) :
    ∀ e, revCong S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ)))
        (Ht.withCap (domCap S (G.withCond fun e => G.cap e ^ 2 / (p e + 1 / (m : ℝ))) Ht)) e
      ≤ Real.sqrt (2 * ξ * m) * (Cf * Real.sqrt ξ * Real.log (S.card : ℝ) ^ (3 / 2 : ℝ)) := by sorry

end FlowSparsSchur.Main
