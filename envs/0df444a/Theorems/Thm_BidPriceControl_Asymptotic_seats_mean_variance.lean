-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_seats_mean_variance
-- name    : BidPriceControl.Asymptotic.seats_mean_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:24.997134+00:00
-- url     : https://prove2.me/theorems/1ad6b191-ced8-4a65-906e-c743f446bd1f
-- title:
--   Mean of Nⁱ is θ Σ_t Σ_j E Y_ijt, and Var(Nⁱ) ≤ θ Σ_t Σ_j Var(Y_ijt) (printed '=' corrected)
-- statement:
--   Assume the standing assumptions of §1, let $\mu^*$ be an optimal solution of (9) for $(x, k)$ and let $\theta \ge 1$ be an integer. In the $\theta$-scaled problem, set $Y_{ijt} = \mathbf{1}\{R_t^j > \mu^* A^j\}\,a_{ij}$ for the original periods $t = 1, \dots, k$, and let $p_{tj} = P(R_t^j > \mu^* A^j)$. The seat count $N^i = \sum_{t=1}^{\theta k}\sum_j \mathbf{1}\{R_t^j(\theta) > \mu^* A^j\}\,a_{ij}$ satisfies
--   $$\mathbb{E} N^i = \theta\sum_{t=1}^k\sum_{j=1}^n \mathbb{E}Y_{ijt} = \theta\sum_{t=1}^k\sum_{j=1}^n p_{tj}\,a_{ij},\qquad \operatorname{Var}(N^i) \le \theta\sum_{t=1}^k\sum_{j=1}^n \operatorname{Var}(Y_{ijt}),$$
--   with $\operatorname{Var}(Y_{ijt}) = a_{ij}^2\,p_{tj}(1 - p_{tj})$.
--
--   **Formalization Note.** The page states $\operatorname{Var}(N^i) = \theta\sum_t\sum_j\operatorname{Var}(Y_{ijt})$. That is false in general. The $Y_{i1t}, \dots, Y_{int}$ of one period are indicators of mutually exclusive events (at most one request per period), so they are negatively correlated. For example, take one leg, two itineraries with $a_{11} = a_{12} = 1$, each arriving above its bid price with probability $1/2$. Then $\sum_j Y = 1$ almost surely, with variance $0$, while $\sum_j \operatorname{Var}(Y) = 1/2$. The inequality is what the proof uses and is what is stated. As on the page, $Y_{ijt}$ uses the bid prices $\mu^*$ of (9). $\operatorname{Var}(N^i)$ is Mathlib's `variance` under the product law; $\operatorname{Var}(Y_{ijt})$ is the closed form `indicatorVar`.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1585, proof of Theorem 1 (mean and variance of Nⁱ; variance identity corrected to ≤)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Mean and variance of `N^i` in the proof of Theorem 1 (p. 1585), with the printed variance
identity corrected to an inequality: for an optimal solution `μ*` of (9) for `(x, k)`, an
integer `θ ≥ 1` and the `θ`-scaled problem with independent periods,
`N^i = ∑_{t=1}^{θk} ∑_j 1{R_t^j(θ) > μ*A^j} a_ij` satisfies
`E N^i = θ ∑_{t=1}^k ∑_j E Y_ijt` and `Var(N^i) ≤ θ ∑_{t=1}^k ∑_j Var(Y_ijt)`, where
`Y_ijt = 1{R_t^j > μ*A^j} a_ij`, `E Y_ijt = P(R_t^j > μ*A^j) a_ij` and
`Var(Y_ijt) = a_ij² P(R_t^j > μ*A^j)(1 − P(R_t^j > μ*A^j))`. (The page prints `Var(N^i) = …`; the
`Y_ijt`, `j = 1, …, n`, of one period are indicators of mutually exclusive events, so only `≤`
holds.) -/
theorem seats_mean_variance {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) (i : Fin m) :
    ∫ ω, seatsCounted A μstar i ω ∂(pathMeasure (scaledLaw F θ) (θ * k))
        = (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) ∧
      variance (seatsCounted A μstar i) (pathMeasure (scaledLaw F θ) (θ * k))
        ≤ (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j := by sorry

end BidPriceControl.Asymptotic
