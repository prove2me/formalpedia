-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_equation_26
-- name    : DistancePreserver934.Exact.equation_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:06.362937+00:00
-- url     : https://prove2.me/theorems/77dbf992-0330-49f2-b906-cab8bec2a298
-- title:
--   §6, Equation (26) — every minimal preserver has $O(n^{8/9}p^{4/9})$ edges for $n^{1/4}\le p\le n$
-- statement:
--   There is an absolute constant $C>0$ such that for every graph $G$ on $n$ vertices and every set $P$ of $p$ unordered demand pairs with
--   $$n^{1/4}\le p\le n,$$
--   every minimal distance preserver $H$ of $(G,P)$ satisfies
--   $$|E_H|\le C\,n^{8/9}p^{4/9}.\tag{26}$$
--
--   This is the stronger statement proved in §6 by strong induction on $p$; it implies Theorem 1. As in §6, the demands may include trivial pairs and pairs in different components, which every subgraph preserves.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, §6, Equation (26), printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- §6, Equation (26), printed p.20 / PDF p.21.  There is an absolute constant `C` such that for
every `n`-vertex graph `G` and every demand set `P` with `n^{1/4} ≤ p = |P| ≤ n`, every minimal
distance preserver `H` of `(G, P)` has `|E_H| ≤ C n^{8/9} p^{4/9}`.  Demands may be trivial or
unreachable here. -/
theorem equation_26 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      IsMinimalPreserver G H P →
      (numEdges H : ℝ) ≤
        C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) := by sorry

end DistancePreserver934.Exact
