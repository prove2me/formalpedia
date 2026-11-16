-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_theorem_27
-- name    : DistancePreserver934.Exact.Supplement.theorem_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:26:18.343668+00:00
-- url     : https://prove2.me/theorems/0003bf87-a2bf-4702-8d17-5965c84731a9
-- title:
--   Theorem 27 — Pairwise +2 spanners with O(n+n^(9/10)p^(2/5)) edges for every p
-- statement:
--   There is an absolute $C>0$ such that every $n$-vertex undirected unweighted graph $G$ and every ordered demand set $P$ of size $p$ admit a spanning additive $+2$ spanner $J\subseteq G$ with
--
--   $$|E(J)|\le C\bigl(n+n^{9/10}p^{2/5}\bigr).$$
--
--   There is no cardinality range restriction. Empty, diagonal, reversed and unreachable pairs are all allowed, as are disconnected and empty graphs. This companion theorem gives the full pairwise additive bound, independently of the exact goal's hypotheses.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 27, printed p. 25 (PDF p. 26)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem theorem_27 :

  ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : Finset (V × V)),
    ∃ J : SimpleGraph V, IsAdditive G J P 2 ∧
      (numEdges J : ℝ) ≤ C * ((Fintype.card V : ℝ) +
        (Fintype.card V : ℝ) ^ ((9 : ℝ) / 10) * (P.card : ℝ) ^ ((2 : ℝ) / 5))
 := by sorry

end DistancePreserver934.Exact.Supplement
