-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_6
-- name    : ContiguousCake597.Approximate.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:15.146891+00:00
-- url     : https://prove2.me/theorems/bd5c5471-ef76-45c2-9d25-47445f67215f
-- title:
--   Lemma 6 — cut localization and both consequences
-- statement:
--   Let $G$ be any nonempty directed graph with every indegree at most two, and use its constructed cake on $[0,L]$. Let $T$ be any complete $\eta$-envy-free allocation with real cuts $\theta$ and arbitrary assignment permutation $\sigma$, where $R=32(s+1)$, $N=32(s+1)^2$, $B=40N$, $L=NB$ and $\eta=1/(100N^2)$ for the number $s$ of graph vertices.
--   Every cut, including the endpoints, satisfies
--   $$|\theta_j-jB|<7N\quad(0\le j\le N).$$
--   The core is $I_j=[(j-1)B+10N,jB-10N]$. For player $v$, put $a_v=vR$, $J_v=[a_vB-13/2,a_vB-11/2]$ and $z_v=\min\{1,\max\{0,\theta_{a_v}-a_vB+13/2\}\}$. Every core $I_j$ is contained in spatial piece $P_j$, and $P_j\cap I_k=\varnothing$ for every $k\ne j$. For every player $v$,
--   $$J_v\subseteq P_{a_v}\cup P_{a_v+1},\qquad |J_v\cap P_{a_v}|=z_v.$$
--   The overlap length is computed exactly as the nonnegative difference between the smaller upper endpoint and larger lower endpoint. This lemma localizes spatial pieces independently of their recipients.
--
--   Differences from the source:
--   - encoding: one-based pieces and interval intersection length → zero-based Fin indices for pieces and an exact endpoint-overlap formula; reason: the spatial piece with index j in Lean is the paper's piece j+1; cuts retain their numbers, including 0 and N
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 9 (PDF 10), Lemma 6

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 6, printed p.9 (PDF 10): every real-cut complete answer,
with arbitrary assignment, satisfies all localization conclusions. -/
theorem lemma_6 (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) ∧
    (∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅) ∧
    (∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v) := by sorry

end ContiguousCake597.Approximate
