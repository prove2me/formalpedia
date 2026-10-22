-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_kuhn_tucker_conditions
-- name    : BidPriceControl.Asymptotic.kuhn_tucker_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:38:43.661809+00:00
-- url     : https://prove2.me/theorems/dbb39753-6275-48be-9403-dc42f3f4d08f
-- title:
--   Kuhn–Tucker conditions (10) for μ*: expected leg demand above the bid prices ≤ capacity, with complementary slackness
-- statement:
--   Assume the standing assumptions of §1; in particular the marginals of $R_t^j$ are continuous on $(0, +\infty)$. Let $\mu^*$ be an optimal solution of (9). Then for every leg $i$,
--   $$\sum_{t=1}^k\sum_{j=1}^n P(R_t^j > \mu^* A^j)\, a_{ij} \le x^i \qquad\text{and}\qquad \mu^{*i}\Big(x^i - \sum_{t=1}^k\sum_{j=1}^n P(R_t^j > \mu^* A^j)\, a_{ij}\Big) = 0.$$
--   In words, the expected number of seats of leg $i$ requested at revenues above the bid prices does not exceed its capacity, and equals it when the leg's bid price is positive.
--
--   **Formalization Note.** The paper prints (10) as $\sum_t\sum_j P(R_t^j > \mu^*A^j)A^j - \lambda = x$, $\lambda\mu^* = 0$, $\lambda \ge 0$. With that sign and $\lambda \ge 0$, expected demand would exceed capacity, which contradicts the paper's own reading of (10) on p. 1584 and its use on p. 1585. The statement uses the corrected sign, slack $\lambda = x - \sum_t\sum_j P(\cdot)A^j \ge 0$, with $\lambda$ eliminated. Only the necessity direction is stated.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1583–1584, eq. (10) (sign of λ corrected)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- The Kuhn–Tucker conditions (10) (pp. 1583–1584), with the sign of the slack corrected: if the
marginals of the `R_t^j` are continuous on `(0, +∞)` (standing assumptions of §1), an optimal
solution `μ*` of (9) satisfies, for every leg `i`,
`∑_{t=1}^k ∑_j P(R_t^j > μ*A^j) a_ij ≤ x^i` and `μ*^i (x^i − ∑_{t=1}^k ∑_j P(R_t^j > μ*A^j) a_ij) = 0`
(the slack `λ^i = x^i − ∑_t ∑_j P(R_t^j > μ*A^j) a_ij ≥ 0` and `λ^i μ*^i = 0`). -/
theorem kuhn_tucker_conditions {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (i : Fin m) :
    ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) ≤ (x i : ℝ) ∧
      μstar i * ((x i : ℝ) - ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))
        = 0 := by sorry

end BidPriceControl.Asymptotic
