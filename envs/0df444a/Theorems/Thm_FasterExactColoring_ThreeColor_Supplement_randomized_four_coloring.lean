-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_randomized_four_coloring
-- name    : FasterExactColoring.ThreeColor.Supplement.randomized_four_coloring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:22.977277+00:00
-- url     : https://prove2.me/theorems/b5db7c18-cdc8-46a8-a435-336abf78c93d
-- title:
--   Theorem 1.4 (companion theorem; not used in the proof of the goal) — randomized four-coloring
-- statement:
--   There is one one-sided Monte Carlo finite program deciding whether any finite simple undirected graph $G$ on $n$ vertices admits a proper four-coloring. For fixed $C>0,d\in\mathbb N$, independent of the graph and its order, every coin tape halts within charged time
--   $$C(n+1)^d(16933/10000)^n=C(n+1)^d1.6933^n.$$
--   The program rejects every no-instance and accepts each yes-instance with probability at least $1/2$. The domain includes empty and disconnected graphs of arbitrary degrees. No certificate feasibility or terminal preprocessing condition is assumed. This is the randomized four-coloring companion result.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs and O* running time → Fin n graph inputs and one charged finite program with C>0 and d in Nat before every n and G; reason: finite labels and uniform polynomial overhead express the same decision bound; empty graphs are included
--   - encoding: one-sided Monte Carlo with a fixed positive input-independent success probability → one-sided acceptance probability at least 1/2 with the charged worst-case bound on all coin tapes; reason: independent constant repetition normalizes success; further charged polynomial amplification handles all subcalls without changing an exponential base
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Theorem 1.4, p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Certificates

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem randomized_four_coloring :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    graphSolver .rand 4 A C d (16933/10000 : ℝ) := by sorry

end FasterExactColoring.ThreeColor.Supplement
