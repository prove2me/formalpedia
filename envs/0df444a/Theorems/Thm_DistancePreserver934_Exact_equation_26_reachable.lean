-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_equation_26_reachable
-- name    : DistancePreserver934.Exact.equation_26_reachable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:12:09.404199+00:00
-- url     : https://prove2.me/theorems/f000b475-2da6-4973-b349-3b1642c5c518
-- title:
--   Equation (26) for distinct reachable demands
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $G$ be a finite simple undirected unweighted graph on $n$ vertices. Let $P$ be a set of $p$ unordered pairs of distinct vertices, each pair reachable in $G$, with $n^{1/4}\le p\le n$. Every inclusion-minimal distance preserver $H\le G$ satisfies
--   $$|E(H)|\le Cn^{8/9}p^{4/9}.$$
--   The constant is chosen before the vertex type, graph and demand set. Subgraphs retain all vertices, and each unordered edge is counted once. Distances use infinity for unreachable pairs.
--
--   This is Equation (26) restricted to the standing demand-set convention of Section 3. The normalization paragraph immediately following Equation (26) reduces arbitrary demands to this case, using Lemma 2 when too few distinct reachable demands remain. This isolates the graph-theoretic induction from that normalization step.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/934.pdf, Section 6 Equation (26) and normalization paragraph, printed p.20 / PDF p.21; standing demand-set convention in Section 3, printed p.8 / PDF p.9.

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- §6, Equation (26), printed p.20 / PDF p.21.  There is an absolute constant `C` such that for
every `n`-vertex graph `G` and every demand set `P` with `n^{1/4} ≤ p = |P| ≤ n`, every minimal
distance preserver `H` of `(G, P)` has `|E_H| ≤ C n^{8/9} p^{4/9}`.  Demands may be trivial or
unreachable here. -/
theorem equation_26_reachable : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      IsDemandSet G P →
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      IsMinimalPreserver G H P →
      (numEdges H : ℝ) ≤
        C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) := by sorry

end DistancePreserver934.Exact
