-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p55_optimal_wholesale_price
-- name    : CachonCoord.MarketClearing.p55_optimal_wholesale_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:42:58.844139+00:00
-- url     : https://prove2.me/theorems/ebeffe22-9e34-454f-a8c8-954d04308182
-- title:
--   §6.5.2, p. 55 — w*(θ) = 1/2 (θ ≤ 3) or 1/4 maximizes π_s, with π_s(w*(θ)) = θ/(2(1 + θ)) or θ/8
-- statement:
--   Let $\theta>1$ and let $\pi_s(w)=q_1(w)w$ if $w\ge\tfrac12-\tfrac1{2\theta}$ and $\pi_s(w)=q_2(w)w$ otherwise, with $q_1,q_2$ as on p. 55. Let $w^*(\theta)=1/2$ if $\theta\le3$ and $1/4$ otherwise. Then $w^*(\theta)$ maximizes $\pi_s$ over $0\le w<1$, and
--   $$
--   \pi_s(w^*(\theta))=\begin{cases}\dfrac{\theta}{2(1+\theta)}&\theta\le3,\\[4pt] \dfrac\theta8&\text{otherwise.}\end{cases}
--   $$
--
--   This is the supplier's best wholesale price contract.
--
--   **Formalization Note** At $\theta=3$ both $1/2$ and $1/4$ give $3/8$; the statement asserts only that $w^*(\theta)$ is a maximizer, not that it is the unique one.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 55, displays π_s(w), w*(θ) and π_s(w*(θ))

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: over the wholesale prices `0 ≤ w < 1`, the supplier's profit `π_s(w)` is maximized at
`w*(θ)` (`1/2` if `θ ≤ 3`, `1/4` otherwise), with `π_s(w*(θ)) = θ/(2(1+θ))` if `θ ≤ 3` and `θ/8`
otherwise. -/
theorem p55_optimal_wholesale_price (θ : ℝ) (hθ : 1 < θ) :
    IsMaxOn (supplierProfit θ) (Set.Ico 0 1) (wStar θ) ∧
    supplierProfit θ (wStar θ) = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) := by sorry

end CachonCoord.MarketClearing
