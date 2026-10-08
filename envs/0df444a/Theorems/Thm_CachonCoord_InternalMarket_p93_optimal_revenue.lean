-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_p93_optimal_revenue
-- name    : CachonCoord.InternalMarket.p93_optimal_revenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:31.521571+00:00
-- url     : https://prove2.me/theorems/53114ef9-f6a3-454d-af13-d2e67f967d3b
-- title:
--   §6.9.1, p. 93 — under the optimal allocation, retailer revenue is π(α, Q) = (α₁^η + α₂^η)^{1/η} Q^{(η−1)/η}
-- statement:
--   Let $\eta>1$, $\alpha_1,\alpha_2>0$ and $Q\ge0$. Conditional on the allocation $\gamma^o(\alpha)=\alpha_1^\eta/(\alpha_1^\eta+\alpha_2^\eta)$, the retailers' total revenue is
--   $$
--   \pi(\alpha,Q)=\pi(\gamma^o(\alpha),\alpha,Q)=(\alpha_1^\eta+\alpha_2^\eta)^{1/\eta}Q^{(\eta-1)/\eta}.
--   $$
--
--   The closed form separates the demand realizations from the output, which is what makes the expected profit (45) a multiple of $e^{(\eta-1)/\eta}$ minus the cost.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 93, the display after Eq. (44)

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 93, the display after (44) (Cachon 2003, 3rd draft): conditional on the optimal
allocation, the retailers' total revenue is
`π(α, Q) = π(γ°(α), α, Q) = (α₁^η + α₂^η)^{1/η} Q^{(η−1)/η}`, for `α₁, α₂ > 0`, `η > 1`, `Q ≥ 0`. -/
theorem p93_optimal_revenue (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 ≤ Q) :
    optRevenue η α₁ α₂ Q = (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ ((η - 1) / η) := by sorry

end CachonCoord.InternalMarket
