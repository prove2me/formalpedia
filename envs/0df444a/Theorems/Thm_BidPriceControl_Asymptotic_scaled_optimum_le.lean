-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_scaled_optimum_le
-- name    : BidPriceControl.Asymptotic.scaled_optimum_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:02.469603+00:00
-- url     : https://prove2.me/theorems/e7ae8932-9c17-4c31-90c9-eb3bddf6d362
-- title:
--   Eq. (13): J_θk(θx) ≤ θ v_k(x)
-- statement:
--   Under the standing assumptions of §1, let $\mu^*$ be an optimal solution of (9) for $(x, k)$, so that $v_k(x) = \bar J_k(x, \mu^*)$. Then for every integer $\theta \ge 1$ the optimal expected revenue of the $\theta$-scaled problem satisfies
--   $$J_{\theta k}(\theta x) \le \theta\, v_k(x).$$
--
--   **Formalization Note.** $J_{\theta k}(\theta x)$ is `optValue` for the scaled laws `scaledLaw F θ`, horizon $\theta k$ and capacity $\theta x$; $v_k(x)$ is `relaxedValue A F k x μstar`.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1585, eq. (13)

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Display (13) of the proof of Theorem 1 (p. 1585): by Lemma 1 and the scaling identity, the optimal
expected revenue of the `θ`-scaled problem satisfies `J_{θk}(θx) ≤ θ v_k(x)`, where
`v_k(x) = J̄_k(x, μ*)` is the optimal value of (9). -/
theorem scaled_optimum_le {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    optValue A (scaledLaw F θ) (θ * k) (θ • x) ≤ (θ : ℝ) * relaxedValue A F k x μstar := by sorry

end BidPriceControl.Asymptotic
