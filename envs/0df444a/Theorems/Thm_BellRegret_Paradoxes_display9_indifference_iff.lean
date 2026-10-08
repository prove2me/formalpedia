-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_display9_indifference_iff
-- name    : BellRegret.Paradoxes.display9_indifference_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:58.680001+00:00
-- url     : https://prove2.me/theorems/c1236398-e90e-4a79-966e-c36fa9116939
-- title:
--   Display (9), p. 974 — full and self insurance are indifferent iff −q + (1 − q)[f(p) − f(−p)] = −p + q[f(1 − p) − f(p − 1)]
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $u(x,y)=x+f(x-y)$, and let $p,q\in\mathbb R$. In Table IV an accident occurs with probability $q$; self insurance loses $1$ on an accident and $0$ otherwise, full insurance loses the premium $p$ in every state. Then full insurance and self insurance are indifferent if and only if
--   $$-q+(1-q)[f(p)-f(-p)]=-p+q[f(1-p)-f(p-1)].\qquad(9)$$
--
--   Equation (9) is the calibration of Kahneman and Tversky's probabilistic-insurance experiment: the decision maker is just indifferent between buying insurance and bearing the risk.
--
--   **Formalization Note** The comparison is made on the three states of Table IV with probabilities $(q/2,q/2,1-q)$ (the accident split by whether the insurer pays); full and self insurance pay the same in both accident states, so this is the two-state comparison of the page. The equivalence holds for every real $p,q$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 974 (PDF 15), Sec. 2(iii), display (9) and Table IV

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Display (9), p. 974: full insurance and self insurance (Table IV) are indifferent if
and only if `−q + (1 − q)[f(p) − f(−p)] = −p + q[f(1 − p) − f(p − 1)]`. -/
theorem display9_indifference_iff (f : ℝ → ℝ) (p q : ℝ) :
    Indiff f (prob3 q) (fullInsurance p) selfInsurance ↔
      -q + (1 - q) * (f p - f (-p)) = -p + q * (f (1 - p) - f (p - 1)) := by sorry

end BellRegret.Paradoxes
