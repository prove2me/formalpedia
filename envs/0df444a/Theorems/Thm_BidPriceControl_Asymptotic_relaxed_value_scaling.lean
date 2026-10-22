-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_relaxed_value_scaling
-- name    : BidPriceControl.Asymptotic.relaxed_value_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:38:19.860178+00:00
-- url     : https://prove2.me/theorems/c9607345-0cb9-4be8-823a-3a3e78a8acb2
-- title:
--   Scaling identity: J̄ of the θ-scaled problem is θ J̄_k(x, μ); μ* solves (9) for every θ
-- statement:
--   Let $\theta \ge 1$ be an integer and consider the $\theta$-scaled problem (12): capacity $\theta x$, horizon $\theta k$ and request laws $R_t(\theta) \sim F_{\lceil t/\theta\rceil}$. For every bid-price vector $\mu$,
--   $$\sum_{t=1}^{\theta k}\sum_{j=1}^n \mathbb{E}\,(R_t^j(\theta) - \mu A^j)^+ + \theta \mu x = \theta\,\bar J_k(x, \mu).$$
--   Consequently every optimal solution $\mu^*$ of (9) for $(x, k)$ is also an optimal solution of (9) for the scaled data $(\theta x, \theta k)$. This is why the heuristic can use the same bid prices in every problem of the sequence.
--
--   **Formalization Note.** Both sides use the closed form (8) of $\bar J$ (`relaxedValue`). The identity is pure reindexing and holds for arbitrary laws $F$, so no standing assumption is imposed.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1585, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- The scaling identity of the proof of Theorem 1 (p. 1585, first display): by (8) and (12), for
every integer `θ ≥ 1` and every bid-price vector `μ`,
`∑_{t=1}^{θk} ∑_j E(R_t^j(θ) − μA^j)^+ + θμx = θ J̄_k(x, μ)`; therefore every minimizer `μ*` of (9)
for `(x, k)` also minimizes (9) for the scaled problem `(θx, θk)`. -/
theorem relaxed_value_scaling {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (θ : ℕ) (hθ : 1 ≤ θ) :
    (∀ μ : Fin m → ℝ,
      relaxedValue A (scaledLaw F θ) (θ * k) (θ • x) μ = (θ : ℝ) * relaxedValue A F k x μ) ∧
    ∀ μstar : Fin m → ℝ, IsRelaxedMinimizer A F k x μstar →
      IsRelaxedMinimizer A (scaledLaw F θ) (θ * k) (θ • x) μstar := by sorry

end BidPriceControl.Asymptotic
