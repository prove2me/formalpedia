-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_three_color_terminal_reduction
-- name    : FasterExactColoring.ThreeColor.Supplement.three_color_terminal_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:27.802843+00:00
-- url     : https://prove2.me/theorems/be3ac963-0776-4848-97c3-ff2a16926ea5
-- title:
--   Lemma 5.2 (used in the proof of Theorem 1.3) — reduction to three-coloring
-- statement:
--   Fix a three-coloring solver with uniform $O^*(\tau^n)$ charged worst-case time on all finite simple graphs. If it is deterministic, the following terminal solver is deterministic; if it is one-sided Monte Carlo, the terminal solver is one-sided Monte Carlo. There are one finite program and constants $C>0,d\in\mathbb N$, fixed for this solver and its base, deciding every valid terminal restricted four-coloring instance within a polynomial in its full encoded size times
--   $$3^{n_{K_3}}4^{n_{K_4}}\tau^{|S|+2n_{K_3}+3n_{K_4}}.$$
--   Here $n_{K_3},n_{K_4}$ count the clique components of $G[U]$. The base is not specialized inside this lemma. Randomized success is at least $1/2$, with no false positives and charged amplification of subcalls. This reduction supplies the terminal alternative using either the published Theorem 1.1 or the new Theorem 1.2.
--
--   Differences from the source:
--   - encoding: terminal instances after the two maximal-star preprocessing steps → valid restricted instances with supplied valid inclusion-maximal star packings, all structural counts computed from them; reason: the explicit finite input includes the graph, restrictions and packings; its size is polynomial in the original vertex count
--   - generalization: deterministic three-coloring solver and terminal reduction → the implication is stated both for deterministic and for one-sided Monte Carlo solvers; reason: the deterministic case is the full printed lemma; Section 5.7 also applies this reduction with Theorem 1.2, with charged amplification as required by Section 2
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.2, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem three_color_terminal_reduction (mode : Mode) (τ : ℝ)
    (h : ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ graphSolver mode 3 A C d τ) :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    terminalSolver mode A C d (fun P _K => threeColorFactor P τ) := by sorry

end FasterExactColoring.ThreeColor.Supplement
