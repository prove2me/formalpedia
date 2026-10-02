-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_log_one_add_div_antitone
-- name    : BJNAdAuctions.Basic.log_one_add_div_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T16:28:03.872348+00:00
-- url     : https://prove2.me/theorems/be5d4a2b-f172-4310-bdcd-659dbb12a828
-- title:
--   Theorem 1, proof, Inequality (3): $\ln(1+x)/x$ is non-increasing on $(0,1]$
-- statement:
--   For real numbers $x, y$ with $0 < x \le y \le 1$,
--   $$
--   \frac{\ln(1+x)}{x} \;\ge\; \frac{\ln(1+y)}{y}.
--   $$
--
--   This elementary inequality is what the proof of Theorem 1 uses to pass from $1 + b(i,k)/B(i)$ to $c^{\,b(i,k)/B(i)}$ in Inequality (3), and it is the reason the constant is chosen as $c = (1+R_{\max})^{1/R_{\max}}$.
--
--   **Formalization Note** The paper allows $x = 0$, where the quotient is read as its limit $1$. In Lean `Real.log 1 / 0 = 0`, so the statement requires $x > 0$.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1, proof, justification of Inequality (3)

import Mathlib

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, the inequality behind Inequality (3) (p. 7): for `0 < x ≤ y ≤ 1`,
`ln(1 + x)/x ≥ ln(1 + y)/y`. The page writes `0 ≤ x`; at `x = 0` the quotient is read as its
limit `1`, whereas Lean's `Real.log 1 / 0 = 0`, so `x > 0` is required. -/
theorem log_one_add_div_antitone (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    Real.log (1 + y) / y ≤ Real.log (1 + x) / x := by sorry

end BJNAdAuctions.Basic
