-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_tree_terminal_algorithm
-- name    : FasterExactColoring.ThreeColor.Supplement.tree_terminal_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:09.498132+00:00
-- url     : https://prove2.me/theorems/10667b48-18c5-4059-b552-28217323ea78
-- title:
--   Lemma 5.5 (used in the proof of Theorem 1.3) — tree-DP terminal algorithm
-- statement:
--   There are one deterministic finite program and constants $C>0,d\in\mathbb N$ deciding every valid terminal restricted four-coloring instance with its valid maximal star packings in a polynomial in its full encoded size times
--   $$24^{s_{\star1}/4}18^{n_{K_3}}24^{n_{K_4}}.$$
--   The quantities count the vertices in the first packing and the triangle and four-clique components of $G[U]$. Correctness respects every edge, including edges between precolored vertices. This terminal bound complements the CSP and three-coloring alternatives.
--
--   Differences from the source:
--   - encoding: terminal instances after the two maximal-star preprocessing steps → valid restricted instances with supplied valid inclusion-maximal star packings, all structural counts computed from them; reason: the explicit finite input includes the graph, restrictions and packings; its size is polynomial in the original vertex count
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.5, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem tree_terminal_algorithm :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    terminalSolver .det A C d (fun P K => treeTerminalFactor P K) := by sorry

end FasterExactColoring.ThreeColor.Supplement
