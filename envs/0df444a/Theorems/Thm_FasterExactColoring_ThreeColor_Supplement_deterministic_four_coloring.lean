-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_deterministic_four_coloring
-- name    : FasterExactColoring.ThreeColor.Supplement.deterministic_four_coloring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:56:33.502316+00:00
-- url     : https://prove2.me/theorems/46187148-7a32-4059-b725-400aad4f5986
-- title:
--   Theorem 1.3 (companion theorem; not used in the proof of the goal) — deterministic four-coloring
-- statement:
--   There is one deterministic finite program deciding whether any finite simple undirected graph $G$ on $n$ vertices admits a proper four-coloring. For fixed constants $C>0,d\in\mathbb N$, independent of the graph and its order, its charged worst-case time is at most
--   $$C(n+1)^d(679/400)^n=C(n+1)^d1.6975^n.$$
--   The graph may be empty, disconnected, or have arbitrary degrees. No terminal-instance, packing, measure-weight or numerical-certificate assumption appears in this theorem. This is the deterministic four-coloring companion result.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs and O* running time → Fin n graph inputs and one charged finite program with C>0 and d in Nat before every n and G; reason: finite labels and uniform polynomial overhead express the same decision bound; empty graphs are included
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Theorem 1.3, p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Certificates

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem deterministic_four_coloring :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    graphSolver .det 4 A C d (679/400 : ℝ) := by sorry

end FasterExactColoring.ThreeColor.Supplement
