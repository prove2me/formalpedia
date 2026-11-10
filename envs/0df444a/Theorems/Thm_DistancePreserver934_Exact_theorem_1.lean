-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_theorem_1
-- name    : DistancePreserver934.Exact.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:57.461719+00:00
-- url     : https://prove2.me/theorems/2861aeb7-3de4-46ce-875f-69d68c0d9b3f
-- title:
--   Theorem 1 — distance preservers with $O(n^{8/9}p^{4/9})$ edges for $n^{1/2}\le p\le n$
-- statement:
--   Let $G=(V,E)$ be any $n$-node undirected unweighted graph and let $P\subseteq V\times V$ be any set of $p$ demand pairs with
--   $$n^{1/2}\le p\le n.$$
--   Then $(G,P)$ admits a distance preserver with $O(n^{8/9}p^{4/9})$ edges: there is an absolute constant $C>0$ such that some spanning subgraph $H\le G$ satisfies
--   $$\operatorname{dist}_H(s,t)=\operatorname{dist}_G(s,t)\quad((s,t)\in P),\qquad|E(H)|\le C\,n^{8/9}p^{4/9}.$$
--
--   The graph need not be connected; demand pairs may be diagonal, reversed or unreachable, and unreachable pairs have distance $\infty$ in both graphs. This improves the bounds of Coppersmith–Elkin and Bodwin–Vassilevska Williams in the range $p\in[n^{7/10},n]$.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Theorem 1, printed p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- Theorem 1, printed p.2 / PDF p.3.  There is an absolute constant `C > 0` such that for every
`n`-node undirected unweighted graph `G` and every set `P ⊆ V × V` of `p` demand pairs with
`n^{1/2} ≤ p ≤ n`, there is a spanning subgraph `H ≤ G` with `dist_H(s,t) = dist_G(s,t)` for
all `(s,t) ∈ P` and `|E(H)| ≤ C n^{8/9} p^{4/9}`. -/
theorem theorem_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (P : Finset (V × V)),
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      ∃ H : SimpleGraph V, H ≤ G ∧ (∀ st ∈ P, H.edist st.1 st.2 = G.edist st.1 st.2) ∧
        (numEdges H : ℝ) ≤
          C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) := by sorry

end DistancePreserver934.Exact
