-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_display11_of_ratio_strictMono
-- name    : BellRegret.Paradoxes.display11_of_ratio_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:09.568392+00:00
-- url     : https://prove2.me/theorems/3cbe4d61-2e7a-4095-8b29-075e95689ad2
-- title:
--   p. 974 — (11) holds if (f(x) − f(−x))/x is increasing in x
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be such that $x\mapsto (f(x)-f(-x))/x$ is strictly increasing on $(0,\infty)$, and let $p>0$. Then
--   $$f(p/2)-f(-p/2)<\tfrac12\,[f(p)-f(-p)].\qquad(11)$$
--
--   The condition is the same one that yields inequalities (5) and (6), so the decision maker who gambles at long odds and buys fair insurance also rejects probabilistic insurance.
--
--   **Formalization Note** "Increasing" is read strictly on $x>0$, as in the item for (5) and (6). The premium $p$ is positive.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 974 (PDF 15), Sec. 2(iii), the sentence after display (11)

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- p. 974: inequality (11) holds if `(f(x) − f(−x))/x` is (strictly) increasing in
`x > 0`, for `p > 0`. -/
theorem display11_of_ratio_strictMono (f : ℝ → ℝ) (p : ℝ)
    (hf : StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0)) (hp : 0 < p) :
    f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) := by sorry

end BellRegret.Paradoxes
