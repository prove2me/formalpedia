-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_explicit_lower_bound
-- name    : BidPriceControl.Asymptotic.explicit_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:39:38.759762+00:00
-- url     : https://prove2.me/theorems/bfc4ed2a-59e7-4c16-89c0-38a2eb7e9522
-- title:
--   Explicit bound: J^H_θk(θx) ≥ θ v_k(x) − (C/2)√θ Σ_i √(Σ_t Σ_j Var(Y_ijt))
-- statement:
--   Assume the standing assumptions of §1 and $R_t^j \le C$ almost surely, and let $\mu^*$ be an optimal solution of (9) for $(x, k)$, so that $v_k(x) = \bar J_k(x, \mu^*)$. Then for every integer $\theta \ge 1$ the fixed-bid-price heuristic with bid prices $\mu^*$ earns, in the $\theta$-scaled problem,
--   $$J^H_{\theta k}(\theta x) \ge \theta\,v_k(x) - \frac{C}{2}\sqrt{\theta}\sum_{i=1}^m\sqrt{\sum_{t=1}^k\sum_{j=1}^n \operatorname{Var}(Y_{ijt})},$$
--   where $Y_{ijt} = \mathbf{1}\{R_t^j > \mu^* A^j\}\,a_{ij}$ and $\operatorname{Var}(Y_{ijt}) = a_{ij}^2\,p_{tj}(1 - p_{tj})$ with $p_{tj} = P(R_t^j > \mu^* A^j)$. This is the paper's $J^H_{\theta k}(\theta x) \ge \theta v_k(x) - O(\sqrt\theta)$ with the explicit constant of p. 1586.
--
--   **Formalization Note.** The constant is carried exactly as printed. $\operatorname{Var}(Y_{ijt})$ is the Bernoulli closed form under the original laws $F_t$, $t = 1, \dots, k$.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1586, proof of Theorem 1, last display

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- The last display of the proof of Theorem 1 (p. 1586): if the revenues are bounded by `C` (a.s.)
and `μ*` is an optimal solution of (9), then for every integer `θ ≥ 1`
`J^H_{θk}(θx) ≥ θ v_k(x) − (C/2) √θ ∑_i √(∑_{t=1}^k ∑_j Var(Y_ijt))`,
where `v_k(x) = J̄_k(x, μ*)` and `Y_ijt = 1{R_t^j > μ*A^j} a_ij`. -/
theorem explicit_lower_bound {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (C : ℝ) (hC : ∀ t ∈ Finset.Icc 1 k, ∀ᵐ r ∂(F t), ∀ j, r j ≤ C)
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    (θ : ℝ) * relaxedValue A F k x μstar
        - C / 2 * Real.sqrt (θ : ℝ) *
          ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j)
      ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by sorry

end BidPriceControl.Asymptotic
