-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_terminal_algorithm_combination
-- name    : FasterExactColoring.ThreeColor.Supplement.terminal_algorithm_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:55:35.422094+00:00
-- url     : https://prove2.me/theorems/00b68d15-88c6-453d-b1d8-127dd859e050
-- title:
--   Lemma 5.8 (used in the proof of Theorem 1.3) — general terminal-algorithm combination
-- statement:
--   Fix $\gamma\ge0$, $r>1$, weights satisfying all of Appendix D, arbitrary finite parameter and algorithm counts $p,a$, fixed matrices $M\in\mathbb R^{3\times p}$ and $R\in\mathbb R^{a\times p}$, and a polynomial-time computable nonnegative vector $x(P)$ for each valid terminal restricted instance. Assume
--   $$Mx(P)=(|S|,n_{K_3},n_{K_4})^\top.$$
--   For each row $R_i$, assume one actual uniform terminal algorithm with time $O^*(\exp(R_i x(P)+\gamma n))$, where $n$ is the original input order. Let $\eta\in\mathbb R^a$ satisfy
--   $$\eta\ge0,\quad\mathbf1^\top\eta=1,\quad
--    \eta^\top R\le(\ln r)(\omega_{c3},\omega_{k3},\omega_{k4})M$$
--   componentwise. Then one uniform finite program decides four-colorability of every graph in time
--   $$O^*((r e^\gamma)^n).$$
--   If the finite portfolio is deterministic, so is the resulting program. If its algorithms are one-sided Monte Carlo, the program has success at least $1/2$ on yes-instances, never accepts no-instances, and has charged worst-case time on every tape. All needed amplification is included. Constants can depend on the fixed weights, matrices, parameter routine and finite portfolio, but never on a graph or its order. The conclusion is algorithm existence, not just the dual scalar inequality. It is not restricted to the eleven-parameter application.
--
--   Differences from the source:
--   - encoding: polynomial-time computable nonnegative real parameter vectors → one deterministic finite program computes dyadic approximations to error 2^(-q) in time polynomial in n+q+1; reason: an explicit precision interface represents real-valued computation without an uncharged exact-real oracle; all finite exact source parameter vectors admit this representation
--   - generalization: deterministic terminal algorithms → the composition is stated in deterministic and one-sided Monte Carlo modes; reason: the deterministic specialization is the printed lemma; the randomized extension is the same composition used in the source Theorem 1.4 application, charging independent amplification
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.8, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Portfolio

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem terminal_algorithm_combination (mode : Mode) {p a : ℕ}
    (γ r : ℝ) (w : Weights) (M : Matrix (Fin 3) (Fin p) ℝ)
    (R : Matrix (Fin a) (Fin p) ℝ) (x : {n : ℕ} → Restricted n → Fin p → ℝ)
    (η : Fin a → ℝ) (hγ : 0 ≤ γ) (hr : 1 < r) (hw : appendixD r w)
    (hcompute : parametersComputable x) (hx : parameterIdentity x M)
    (hportfolio : terminalPortfolio mode γ x R) (hdual : dualComparison r w M R η) :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    graphSolver mode 4 A C d (r*Real.exp γ) := by sorry

end FasterExactColoring.ThreeColor.Supplement
