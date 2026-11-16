-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_theorem_36
-- name    : DistancePreserver934.Exact.Supplement.theorem_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:12.632271+00:00
-- url     : https://prove2.me/theorems/5b62906a-dbf4-4702-8f56-33ba19412e55
-- title:
--   Theorem 36 — Pairwise +4 spanners with O(n+n^(24/25)p^(8/25)) edges for p≤n^(7/6)
-- statement:
--   There is an absolute $C>0$ such that any $n$-vertex graph $G$ and arbitrary ordered demand set $P$ of size $p\le n^{7/6}$ admit a spanning additive $+4$ spanner with
--
--   $$|E(J)|\le C\bigl(n+n^{24/25}p^{8/25}\bigr).$$
--
--   The full range includes $p>n$ as well as empty demands and empty graphs; disconnected graphs, diagonal pairs and unreachable demands are retained. This companion theorem uses the shared sampling and completion reductions and the published exact-preserver bounds.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 36, printed p. 32 (PDF p. 33)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem theorem_36 :

  ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : Finset (V × V)),
    (P.card : ℝ) ≤ (Fintype.card V : ℝ) ^ ((7 : ℝ) / 6) →
    ∃ J : SimpleGraph V, IsAdditive G J P 4 ∧
      (numEdges J : ℝ) ≤ C * ((Fintype.card V : ℝ) +
        (Fintype.card V : ℝ) ^ ((24 : ℝ) / 25) * (P.card : ℝ) ^ ((8 : ℝ) / 25))
 := by sorry

end DistancePreserver934.Exact.Supplement
