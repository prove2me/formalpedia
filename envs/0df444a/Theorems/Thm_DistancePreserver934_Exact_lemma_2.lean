-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_2
-- name    : DistancePreserver934.Exact.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:48.94961+00:00
-- url     : https://prove2.me/theorems/cf2a4dbd-3771-42fb-ae66-c056c8bbb504
-- title:
--   Lemma 2 ([CE06]) — every minimal preserver has $O(n+p\sqrt n)$ edges
-- statement:
--   Let $G$ be a graph on $n$ vertices and $R$ a demand set of $p$ unordered pairs of distinct connected vertices. There is an absolute constant $C>0$ such that every minimal distance preserver $H$ of $(G,R)$ satisfies
--   $$|E_H|\le C\,(n+p\sqrt n).$$
--
--   The bound holds for every inclusion-minimal preserver, not only for a well-chosen one; Section 6 uses it in the base case of the induction and for small residual demand sets (Equation (31)).
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 2, printed p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 2 ([CE06]), printed p.8 / PDF p.9: every minimal distance preserver of an
`n`-vertex graph with `p` demand pairs has `O(n + p √n)` edges, with one absolute constant. -/
theorem lemma_2 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)),
      IsDemandSet G R → IsMinimalPreserver G H R →
      (numEdges H : ℝ) ≤
        C * ((Fintype.card V : ℝ) + (R.card : ℝ) * Real.sqrt (Fintype.card V : ℝ)) := by sorry

end DistancePreserver934.Exact
