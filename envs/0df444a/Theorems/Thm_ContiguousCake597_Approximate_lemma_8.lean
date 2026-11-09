-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_8
-- name    : ContiguousCake597.Approximate.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:27.576613+00:00
-- url     : https://prove2.me/theorems/57ba77b9-50cc-49f0-9f18-62fbd1baca6b
-- title:
--   Lemma 8 — constructed prices satisfy both clauses of (3)
-- statement:
--   Let $G$ be any nonempty directed graph with every indegree at most two, and use its constructed cake on $[0,L]$. Let $T$ be any complete $\eta$-envy-free allocation with real cuts $\theta$ and arbitrary assignment permutation $\sigma$, where $R=32(s+1)$, $N=32(s+1)^2$, $B=40N$, $L=NB$ and $\eta=1/(100N^2)$ for the number $s$ of graph vertices.
--   Let $\ell_j=\theta_j-\theta_{j-1}$ and $z_v=\min\{1,\max\{0,\theta_{vR}-vRB+13/2\}\}$. For the disjoint constructed sets $S_v$, put $q_j=\ell_j+z_v$ when $j\in S_v$ and $q_j=\ell_j$ otherwise. With $U_i$ the constructed interval valuation and $\pi$ the constructed single-cycle successor, both assertions of equation (3) hold:
--   $$U_i(P_j)-U_i(P_i)\le q_j-q_i\quad\text{for all }i,j,$$
--   $$U_i(P_{\pi(i)})-U_i(P_i)=q_{\pi(i)}-q_i\quad\text{for all }i.$$
--   The prices and successor cycle are the explicit construction. Neither localization nor these inequalities are hypotheses. The equality is needed to connect approximate envy-freeness to the standalone price-range lemma.
--
--   Differences from the source:
--   - encoding: the pieces satisfy (3) with these prices → both displayed clauses of (3), with the defined prices substituted; reason: expands the source cross-reference, preserving its universal inequality and exact equality
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 10 (PDF 11), Lemma 8; equation (3), p.9 (PDF 10)

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 8, printed p.10 (PDF 11), with BOTH clauses of Eq. (3)
printed p.9 (PDF 10). Localization is a consequence, never a hypothesis. -/
theorem lemma_8 (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ i j : Fin (N G),
      pieceValue G T i j - pieceValue G T i i ≤ price G T j - price G T i) ∧
    (∀ i : Fin (N G),
      pieceValue G T i (pi G i) - pieceValue G T i i =
        price G T (pi G i) - price G T i) := by sorry

end ContiguousCake597.Approximate
