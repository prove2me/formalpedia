-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_display6_insurance_iff_bet
-- name    : BellRegret.Paradoxes.display6_insurance_iff_bet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:50.741026+00:00
-- url     : https://prove2.me/theorems/a2d05e1a-f6e0-4680-bb16-6ca18bb4f4e7
-- title:
--   Display (6), p. 972 — fair insurance is preferred iff (6), and (5) and (6) are identical
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $u(x,y)=x+f(x-y)$, and let $p\in\mathbb R$. A car is damaged with probability $p$, at a repair cost of $\$1$; insurance costs a premium of $\$p$ (Table III). Then
--
--   1. insuring is strictly preferred to not insuring if and only if
--   $$p\,[f(1-p)-f(p-1)]>(1-p)\,[f(p)-f(-p)],\qquad(6)$$
--   2. and consequently insuring is strictly preferred to not insuring if and only if the bet of Table II is strictly preferred to not betting.
--
--   Inequality (6) is literally inequality (5): a decision maker who prefers the fair long-odds bet necessarily also buys the fair insurance.
--
--   **Formalization Note** Both equivalences are algebraic identities and hold for every real $p$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 972 (PDF 13), Sec. 2(i), Table III, display (6) and "Note that inequalities (5) and (6) are identical"

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Display (6) and "(5) and (6) are identical", p. 972: insuring (Table III) is strictly
preferred to not insuring if and only if `p[f(1 − p) − f(p − 1)] > (1 − p)[f(p) − f(−p)]`;
hence insuring is strictly preferred exactly when the bet of Table II is. -/
theorem display6_insurance_iff_bet (f : ℝ → ℝ) (p : ℝ) :
    (Prefers f (prob2 p) (carInsure p) carNoInsure ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p))) ∧
    (Prefers f (prob2 p) (carInsure p) carNoInsure ↔
      Prefers f (prob2 p) (horseBet p) horseNoBet) := by sorry

end BellRegret.Paradoxes
