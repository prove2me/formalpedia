-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_display5_bet_iff
-- name    : BellRegret.Paradoxes.display5_bet_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:54.463985+00:00
-- url     : https://prove2.me/theorems/b1d888c2-5999-472b-9a51-5a055c71a7bf
-- title:
--   Display (5), p. 971 — the long-odds bet is preferred iff p[f(1 − p) − f(p − 1)] > (1 − p)[f(p) − f(−p)]
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $u(x,y)=x+f(x-y)$, and let $p\in\mathbb R$. A horse wins with probability $p$; a bet of $\$p$ returns a net $\$(1-p)$ if it wins and $-\$p$ if it loses, while not betting gives $\$0$ in both states (Table II). Then the bet is strictly preferred to not betting if and only if
--   $$p\,[f(1-p)-f(p-1)]>(1-p)\,[f(p)-f(-p)].\qquad(5)$$
--
--   Both alternatives have the same expected value, so the comparison reduces to the regret terms alone. This is the first half of Bell's explanation of the coexistence of insurance and gambling.
--
--   **Formalization Note** The equivalence is an algebraic identity and holds for every real $p$; the paper's range $0<p<\tfrac12$ is not needed here and is imposed where it is used.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 971 (PDF 12), Sec. 2(i), Table II and display (5)

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Display (5), p. 971: with `u(x, y) = x + f(x − y)`, the bet of Table II is strictly
preferred to not betting if and only if `p[f(1 − p) − f(p − 1)] > (1 − p)[f(p) − f(−p)]`. -/
theorem display5_bet_iff (f : ℝ → ℝ) (p : ℝ) :
    Prefers f (prob2 p) (horseBet p) horseNoBet ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by sorry

end BellRegret.Paradoxes
