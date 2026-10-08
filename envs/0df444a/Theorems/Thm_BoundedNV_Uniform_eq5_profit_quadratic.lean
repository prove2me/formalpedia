-- Prove2me | Theorems.Thm_BoundedNV_Uniform_eq5_profit_quadratic
-- name    : BoundedNV.Uniform.eq5_profit_quadratic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:27.629682+00:00
-- url     : https://prove2.me/theorems/801013d9-3621-4acf-8fc8-51197d8b9d80
-- title:
--   §4.1, eq. (5), p. 572 — under uniform demand the expected profit is quadratic on [a, b]
-- statement:
--   Let the demand $D$ be uniformly distributed on $[a, b]$ with $b > a \ge 0$, and let $0 < c < p$. For every order quantity $x \in [a, b]$, the newsvendor's expected profit $\pi(x) = p\,\mathbb E\min(D,x) - cx$ is the quadratic
--   $$\pi(x) = A x^2 + B x + C, \qquad A = -\frac{p}{2(b-a)},\quad B = \frac{pb}{b-a} - c,\quad C = -\frac{p a^2}{2(b-a)}.$$
--
--   This quadratic structure is what makes the logit density $e^{\pi(x)/\beta}$ a Gaussian kernel on $[a, b]$, which is the content of Proposition 1.
--
--   **Formalization Note** The paper states (5) without restricting $x$; it holds only on $[a, b]$, since $\pi(x) = (p-c)x$ for $x < a$ and $\pi(x) = p(a+b)/2 - cx$ for $x > b$. The decision domain of the behavioral solution is $[a, b]$, so this is the range on which (5) is used.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 572 (PDF 7), §4.1, eq. (5)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

namespace BoundedNV.Uniform

/-- §4.1, eq. (5), p. 572: for demand `D ∼ U[a, b]` with `0 ≤ a < b`, on the interval `[a, b]` the
expected profit (3) is the quadratic `A x² + B x + C` with `A = −p/(2(b − a))`,
`B = pb/(b − a) − c` and `C = −pa²/(2(b − a))`. -/
theorem eq5_profit_quadratic (a b p c : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    ∀ x ∈ Set.Icc a b,
      nvProfit (unifDensity a b) p c x =
        (-p / (2 * (b - a))) * x ^ 2 + (p * b / (b - a) - c) * x + (-p * a ^ 2 / (2 * (b - a))) := by sorry

end BoundedNV.Uniform
