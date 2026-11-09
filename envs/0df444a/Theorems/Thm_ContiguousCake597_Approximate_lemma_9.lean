-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_9
-- name    : ContiguousCake597.Approximate.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:35.198566+00:00
-- url     : https://prove2.me/theorems/b3f24351-f6d6-4ef0-83fa-9f38c0833a14
-- title:
--   Lemma 9 — decoding with error at most 1/100
-- statement:
--   Let $G$ be any nonempty directed graph with every indegree at most two, and use its constructed cake on $[0,L]$. Let $T$ be any complete $\eta$-envy-free allocation with real cuts $\theta$ and arbitrary assignment permutation $\sigma$, where $R=32(s+1)$, $N=32(s+1)^2$, $B=40N$, $L=NB$ and $\eta=1/(100N^2)$ for the number $s$ of graph vertices.
--   Put $a_v=vR$ and $z_v=\min\{1,\max\{0,\theta_{a_v}-a_vB+13/2\}\}$. For every player $u$ this explicitly decoded vector satisfies
--   $$\left|\theta_{a_u}-a_uB+12(Az)_u\right|\le\frac1{100}.$$
--   Here $(Az)_u$ sums the decoded strategies of the incoming neighbors of $u$, with a self-loop counted once. The sign is positive in this absolute-value formula. No equilibrium property, price inequality or localization property is assumed. This is the quantitative estimate used by the final threshold-game decoder.
--
--   Differences from the source:
--   - encoding: matrix row u is the in-neighbor set → the sum over graph edges v→u; reason: the published graph adjacency arguments are transposed relative to the paper's matrix convention
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 10 (PDF 11), Lemma 9, proof continues p.11 (PDF 12)

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 9, printed p.10 (PDF 11), proof continues on printed p.11
(PDF 12). The sign and constant are literal. -/
theorem lemma_9 (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    ∀ u : Fin G.n,
      |T.cuts (specialPiece G u).succ - (a G u : ℝ) * B G +
        12 * incoming G T u| ≤ 1/100 := by sorry

end ContiguousCake597.Approximate
