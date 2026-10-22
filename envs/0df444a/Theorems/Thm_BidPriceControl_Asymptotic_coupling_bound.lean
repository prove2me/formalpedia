-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_coupling_bound
-- name    : BidPriceControl.Asymptotic.coupling_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:14.699762+00:00
-- url     : https://prove2.me/theorems/01b35b4c-f9e0-4902-aae4-3a18e46fecf5
-- title:
--   Coupling bound (14): J^H_θk(θx) ≥ Σ E(R − μ*A^j)⁺ + Σ P(R > μ*A^j)μ*A^j − C Σ_i E(Nⁱ − θxⁱ)⁺
-- statement:
--   Assume the standing assumptions of §1 and $R_t^j \le C$ almost surely. Let $\mu^*$ be an optimal solution of (9) for $(x, k)$ and let $\theta \ge 1$ be an integer. The fixed-bid-price heuristic with bid prices $\mu^*$ in the $\theta$-scaled problem earns
--   $$J^H_{\theta k}(\theta x) \ge \sum_{t=1}^{\theta k}\sum_{j=1}^n \mathbb{E}\,(R_t^j(\theta) - \mu^* A^j)^+ + \sum_{t=1}^{\theta k}\sum_{j=1}^n P(R_t^j(\theta) > \mu^* A^j)\,\mu^* A^j - C\sum_{i=1}^m \mathbb{E}\,(N^i - \theta x^i)^+,$$
--   where $N^i = \sum_{t=1}^{\theta k}\sum_{j=1}^n \mathbf{1}\{R_t^j(\theta) > \mu^* A^j\}\,a_{ij}$. The first two terms are the revenue of an alternate system that accepts every request above its bid price and ignores capacity. The last term charges $C$ for each seat that system sells beyond a leg's capacity.
--
--   **Formalization Note.** As on the page, the bid prices are an optimal solution $\mu^*$ of (9) (a predicate, `IsRelaxedMinimizer`, so every minimizer is covered). The page calls $N^i$ "the number of leg $i$ seats sold under the bid-price heuristic", but its displayed formula counts every request above the threshold, which is the alternate system's seat count. The displayed formula is formalized (`seatsCounted`), as a random variable on the path space of the $\theta k$ periods.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1585, eq. (14)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- The coupling bound (14) of the proof of Theorem 1 (p. 1585): if the revenues are bounded by `C`
(a.s.) and `μ*` is an optimal solution of (9) for `(x, k)`, the expected revenue of the
fixed-bid-price heuristic with bid prices `μ*` in the `θ`-scaled problem satisfies
`J^H_{θk}(θx) ≥ ∑_{t=1}^{θk} ∑_j E(R_t^j(θ) − μ*A^j)^+ + ∑_{t=1}^{θk} ∑_j P(R_t^j(θ) > μ*A^j) μ*A^j
 − C ∑_i E(N^i − θx^i)^+`,
where `N^i = ∑_{t=1}^{θk} ∑_j 1{R_t^j(θ) > μ*A^j} a_ij` counts the leg-`i` seats of the uncapacitated
alternate system. -/
theorem coupling_bound {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (C : ℝ) (hC : ∀ t ∈ Finset.Icc 1 k, ∀ᵐ r ∂(F t), ∀ j, r j ≤ C)
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    (∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, ∫ r, max (r j - bidSum A μstar j) 0 ∂(scaledLaw F θ t))
      + (∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j)
      - C * ∑ i, ∫ ω, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0
          ∂(pathMeasure (scaledLaw F θ) (θ * k))
      ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by sorry

end BidPriceControl.Asymptotic
