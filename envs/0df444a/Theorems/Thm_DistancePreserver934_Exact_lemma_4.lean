-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_4
-- name    : DistancePreserver934.Exact.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:51.821502+00:00
-- url     : https://prove2.me/theorems/f705d55f-cd1c-4190-b477-dee9c7ae3b40
-- title:
--   Lemma 4 (adapted from [BW21]) — induced edges of a minimal preserver with sources in $S$
-- statement:
--   Let $G$ be a graph, $S$ a nonempty vertex set with $\sigma=|S|$ and $\operatorname{diam}_G(S)\le d$ (diameter measured in $G$, finite), and $R$ a demand set of $p$ pairs each having an endpoint in $S$. There is an absolute constant $C>0$ such that for every minimal distance preserver $H$ of $(G,R)$ and every vertex set $U$ of size $k$,
--   $$|E_H^U|\le C\left(k+\sqrt{k\,p\,\sigma\,d}\right),$$
--   where $E_H^U$ is the edge set of the induced subgraph $H[U]$.
--
--   The statement covers $k=0$, singleton $S$ and $d=0$. Lemma 3 is the case $U=V$. Lemma 4 bounds the preserver of split demands in Lemmas 17 and 21.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
--   - encoding: ordered demand set P ⊆ S × V of size p → unordered demand set R in which every pair has an endpoint in S, p = |R|; reason: orienting each unordered pair from an endpoint in S gives P with |P| = |R|, and merging reversed ordered pairs gives |R| ≤ |P|; preservers and their minimality are the same, and the bound is monotone in p
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 4 (proof in Appendix A, printed pp. 38–39, PDF pp. 39–40), printed p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 4 (adapted from [BW21]), printed p.9 / PDF p.10.  `S` nonempty with
`diam_G(S) ≤ d`, every demand has an endpoint in `S`, `H` a minimal distance preserver of
`(G, R)`; then for every vertex set `U` of size `k`, `|E_H^U| = O(k + √(k p σ d))`. -/
theorem lemma_4 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (S : Finset V) (d : ℝ)
      (R : Finset (Sym2 V)) (U : Finset V),
      S.Nonempty → DiamLE G S d → IsDemandSet G R →
      (∀ s t : V, s(s, t) ∈ R → s ∈ S ∨ t ∈ S) →
      IsMinimalPreserver G H R →
      ((inducedEdges H U).card : ℝ) ≤
        C * ((U.card : ℝ) +
          Real.sqrt ((U.card : ℝ) * (R.card : ℝ) * (S.card : ℝ) * d)) := by sorry

end DistancePreserver934.Exact
