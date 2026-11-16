-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_path_terminal_algorithm
-- name    : FasterExactColoring.ThreeColor.Supplement.path_terminal_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:56:59.539933+00:00
-- url     : https://prove2.me/theorems/80d410d5-dec9-4f30-a00f-d3e8f3fdc308
-- title:
--   Lemma 5.6 (used in the proof of Theorem 1.4) — randomized path-DP terminal algorithm
-- statement:
--   For every fixed $\epsilon>0$, there are one one-sided Monte Carlo finite program and constants $C>0,d\in\mathbb N$ deciding every valid terminal restricted four-coloring instance with its valid maximal star packings in a polynomial in encoded input size times
--   $$Q\,3^{(10/3)b_0+2(a_0+b_1)+(a_1+b_2)+(a_2+b_3)/2+\epsilon n}.$$
--   Here $n$ is the original order, $Q=24^{s_{\star1}/4}\prod_{i=0}^3 Q_i^{a_i}\prod_{i=0}^4 Q_i^{b_i}$, $Q_0=1$, and
--   $$Q_i=\frac{6\,8^i}{(4-i)!}(4-i+27i/8)\quad(1\le i\le4).$$
--   The program never accepts no-instances, succeeds with probability at least $1/2$ on each yes-instance, and meets the charged worst-case bound on every tape. The program and polynomial constants may depend on $\epsilon$ only, before all instances and packings. This is the additional path-DP terminal alternative used by Theorem 1.4.
--
--   Differences from the source:
--   - encoding: terminal instances after the two maximal-star preprocessing steps → valid restricted instances with supplied valid inclusion-maximal star packings, all structural counts computed from them; reason: the explicit finite input includes the graph, restrictions and packings; its size is polynomial in the original vertex count
--   - encoding: one-sided Monte Carlo with a fixed positive input-independent success probability → one-sided acceptance probability at least 1/2 with the charged worst-case bound on all coin tapes; reason: independent constant repetition normalizes success; further charged polynomial amplification handles all subcalls without changing an exponential base
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.6, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem path_terminal_algorithm (ε : ℝ) (hε : 0 < ε) :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    terminalSolver .rand A C d (fun P K => pathTerminalFactor P K ε) := by sorry

end FasterExactColoring.ThreeColor.Supplement
