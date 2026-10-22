-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_bid_price_revenue_identity
-- name    : BidPriceControl.Asymptotic.bid_price_revenue_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:31.781325+00:00
-- url     : https://prove2.me/theorems/29778f3d-0646-4fc1-8ef1-257e97fd7bba
-- title:
--   Eq. (16): Σ_{t≤θk} Σ_j P(R_t^j(θ) > μ*A^j) μ*A^j = θ μ*x
-- statement:
--   Assume the standing assumptions of §1 and let $\mu^*$ be an optimal solution of (9) for $(x, k)$. For every integer $\theta \ge 1$,
--   $$\sum_{t=1}^{\theta k}\sum_{j=1}^n P(R_t^j(\theta) > \mu^* A^j)\,\mu^* A^j = \theta\,\mu^* x.$$
--   Complementary slackness in (10) says that legs with a positive bid price are exactly filled in expectation. So the expected bid-price value of the requests the alternate system accepts equals the bid-price value of the scaled capacity.
--
--   **Formalization Note.** $P(R_t^j(\theta) > \cdot)$ is `exceedProb` under the scaled laws `scaledLaw F θ`; $\mu^* x = \sum_i \mu^{*i} x^i$.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1586, eq. (16)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Display (16) of the proof of Theorem 1 (p. 1586): by the Kuhn–Tucker conditions (10), for an
optimal solution `μ*` of (9) for `(x, k)` and every integer `θ ≥ 1`,
`μ*(∑_{t=1}^{θk} ∑_j P(R_t^j(θ) > μ*A^j) A^j − θx) = 0`, so that
`∑_{t=1}^{θk} ∑_j P(R_t^j(θ) > μ*A^j) μ*A^j = θ μ*x`. -/
theorem bid_price_revenue_identity {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (F : ℕ → Measure (Fin n → ℝ)) (k : ℕ) (x : Fin m → ℕ)
    (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    ∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j
      = (θ : ℝ) * ∑ i, μstar i * (x i : ℝ) := by sorry

end BidPriceControl.Asymptotic
