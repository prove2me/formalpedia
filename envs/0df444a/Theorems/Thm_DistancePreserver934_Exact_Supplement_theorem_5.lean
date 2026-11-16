-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_theorem_5
-- name    : DistancePreserver934.Exact.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:40.895377+00:00
-- url     : https://prove2.me/theorems/6de774d4-d88a-46a1-8378-eb083d46e405
-- title:
--   Theorem 5 — Every edge-disjoint minimal preserver has O(n^(5/6)p^(1/2)) edges in its full range
-- statement:
--   There is an absolute $C>0$ such that every $n$-vertex undirected unweighted graph $G$, technical unordered demand set $P$ of size $n^{2/3}\le p\le n$, and inclusion-minimal preserver $H\subseteq G$ containing mutually edge-disjoint shortest paths for the demands satisfy
--
--   $$|E(H)|\le Cn^{5/6}p^{1/2}.$$
--
--   This bounds every admissible $H$, rather than asserting existence of a specially chosen sparse one. No connectedness, regularity or shortest-path uniqueness is assumed. Empty graphs remain included. This companion theorem is separate from the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 5, printed p. 9 (PDF p. 10)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem theorem_5 :

  ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (P : Finset (Sym2 V))
    (_π : EdgeDisjointFamily H P),
    IsDemandSet G P → IsMinimalPreserver G H P →
    (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ (P.card : ℝ) →
    P.card ≤ Fintype.card V →
    (numEdges H : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 6) *
      (P.card : ℝ) ^ ((1 : ℝ) / 2)
 := by sorry

end DistancePreserver934.Exact.Supplement
