-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_overflow_bound
-- name    : BidPriceControl.Asymptotic.overflow_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:22.549735+00:00
-- url     : https://prove2.me/theorems/19137bfa-183e-444e-a8e1-01cf3b09d6e5
-- title:
--   Eq. (15): E(Nⁱ − θxⁱ)⁺ ≤ √Var(Nⁱ)/2
-- statement:
--   Assume the standing assumptions of §1, let $\mu^*$ be an optimal solution of (9) for $(x, k)$, and let $\theta \ge 1$ be an integer. In the $\theta$-scaled problem let $N^i = \sum_{t=1}^{\theta k}\sum_j \mathbf{1}\{R_t^j(\theta) > \mu^* A^j\}\,a_{ij}$. Then for every leg $i$,
--   $$\mathbb{E}\,(N^i - \theta x^i)^+ \le \frac{\sqrt{\operatorname{Var}(N^i)}}{2}.$$
--   The expected overflow of the uncapacitated system on each leg thus grows at most like a standard deviation, that is, like $\sqrt\theta$, while revenues grow like $\theta$.
--
--   **Formalization Note.** $\mathbb{E}$ and $\operatorname{Var}$ are taken under the product law of the $\theta k$ scaled periods (`pathMeasure`). No bound $C$ is needed.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1585–1586, eq. (15)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Display (15) of the proof of Theorem 1 (pp. 1585–1586): for an optimal solution `μ*` of (9) and
the `θ`-scaled problem, `E(N^i − θx^i)^+ ≤ √Var(N^i) / 2` for every leg `i`, where
`N^i = ∑_{t=1}^{θk} ∑_j 1{R_t^j(θ) > μ*A^j} a_ij`. -/
theorem overflow_bound {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ)
    (i : Fin m) :
    ∫ ω, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0
        ∂(pathMeasure (scaledLaw F θ) (θ * k))
      ≤ Real.sqrt (variance (seatsCounted A μstar i) (pathMeasure (scaledLaw F θ) (θ * k))) / 2 := by sorry

end BidPriceControl.Asymptotic
