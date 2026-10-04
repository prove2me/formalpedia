-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_lemmaA_1_log_inequality
-- name    : BalcanDDA.Piecewise.lemmaA_1_log_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:57:58.967486+00:00
-- url     : https://prove2.me/theorems/1e13cc5b-46ba-4900-b2dc-6e4d451ab5cf
-- title:
--   Lemma A.1 — $y < a\ln y + b \Rightarrow y < 4a\ln(2a) + 2b$
-- statement:
--   Let $a \ge 1$ and $b > 0$ be real numbers. If a real number $y$ satisfies $y < a \ln y + b$, then
--   $$y < 4a\ln(2a) + 2b.$$
--
--   This elementary inequality (from Shalev-Shwartz and Ben-David's textbook) converts an implicit bound of the form "$N \le a\ln N + b$" into an explicit one; it turns the shattering inequality into the explicit pseudo-dimension bound of Theorem 3.3.
--
--   **Formalization Note.** The statement is made for every real $y$. For $y \le 0$, where Lean's `Real.log` takes junk values, the conclusion holds anyway because its right side is positive ($a \ge 1$, $b > 0$), so nothing is added or lost.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 50, Lemma A.1

import Mathlib

namespace BalcanDDA.Piecewise

/-- Lemma A.1 (Balcan et al., arXiv:1908.02894v4, p. 50; Shalev-Shwartz and Ben-David).
Let `a ≥ 1` and `b > 0`. If `y < a ln y + b`, then `y < 4a ln(2a) + 2b`. Stated for every real
`y`; for `y ≤ 0` the conclusion holds because its right side is positive. -/
theorem lemmaA_1_log_inequality (a b y : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (hy : y < a * Real.log y + b) :
    y < 4 * a * Real.log (2 * a) + 2 * b := by sorry

end BalcanDDA.Piecewise
