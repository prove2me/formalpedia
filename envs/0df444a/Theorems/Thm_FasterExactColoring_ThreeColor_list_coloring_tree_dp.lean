-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_list_coloring_tree_dp
-- name    : FasterExactColoring.ThreeColor.list_coloring_tree_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:20.336888+00:00
-- url     : https://prove2.me/theorems/6cef0723-ece3-4ee9-9790-8b9ccb4a1925
-- title:
--   Lemma 3.4 (corrected: zero palette and empty graph) — list-coloring tree DP
-- statement:
--   Given any finite graph $G$, nonnegative color count $k$, arbitrary allowed-color lists $L(v)\subseteq\{0,\ldots,k-1\}$, and a valid supplied tree decomposition of integer width $w$, one deterministic program decides list colorability in time
--   $$O^*(k^w).$$
--   The coefficient and polynomial degree are uniform over all inputs; the polynomial factor charges the graph, palette, lists and complete tree-decomposition description. Empty lists are allowed. At empty-graph or zero-palette boundaries the time envelope is interpreted as $(\max\{1,k\})^{\max\{0,w\}}$, so trivial acceptance or rejection has a nonzero allowance. This is the general decomposition algorithm, with no specialization to three colors.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - correction: O*(k^tw) for a nonnegative palette size k, including zero, and integer width tw → O*(max(1,k)^max(0,tw)), retaining all palette sizes and empty graphs; reason: at k=0 a graph consisting of one edge with its single two-vertex bag has tw=1 and printed factor zero, although every charged execution costs at least one; an empty graph has width -1 and 0^-1 is undefined; this is the minimal positive time envelope on those boundary instances
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 3.4, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds
import Definitions.Def_FasterExactColoring_ThreeColor_Decompositions

namespace FasterExactColoring.ThreeColor

/-- Corrected boundary of Lemma 3.4: k=0 and a single edge with a two-vertex bag give k^tw=0, so use the positive lower envelope; the ordinary positive-palette, nonnegative-width bound is unchanged. -/
theorem list_coloring_tree_dp :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic A ∧
    ∀ (n k : ℕ) (G : GraphInput n) (L : Fin n → Finset (Fin k))
      (D : TreeData n), D.valid G →
      let x := graphCode G ++ listCode L ++ D.code
      runWithin A x (polynomial C d x * widthFactor k D.width)
        (answers (listColorable G L)) := by sorry

end FasterExactColoring.ThreeColor
