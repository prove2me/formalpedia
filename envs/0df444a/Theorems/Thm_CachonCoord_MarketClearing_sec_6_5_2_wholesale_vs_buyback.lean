-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_sec_6_5_2_wholesale_vs_buyback
-- name    : CachonCoord.MarketClearing.sec_6_5_2_wholesale_vs_buyback
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:54:05.258733+00:00
-- url     : https://prove2.me/theorems/10756588-93e8-455d-b841-f6d8c07fae3d
-- title:
--   §6.5.2, pp. 55–57 — the best wholesale price earns θ/(2(1 + θ)) or θ/8 < Π° = (1 + θ)/8; the buy-back b = w = 1/2 earns Π°
-- statement:
--   Let $\theta>1$, with market clearing prices $p_l(q)=(1-q)^+$, $p_h(q)=(1-q/\theta)^+$ in two equally likely states, perfectly competitive retailers, zero salvage value and zero production cost. Write
--   $$
--   \pi_s^*=\begin{cases}\dfrac{\theta}{2(1+\theta)}&\theta\le3,\\[4pt]\dfrac\theta8&\theta>3.\end{cases}
--   $$
--   Then:
--   1. $\pi_s^*$ is the greatest profit $wq$ the supplier can obtain with a wholesale price contract, over all prices $w$ and the competitive total order $q$ at $w$;
--   2. at $w^*(\theta)$ ($1/2$ if $\theta\le3$, $1/4$ otherwise) a competitive order exists and every competitive order $q$ gives $w^*(\theta)q=\pi_s^*$;
--   3. the monopolist's maximal expected profit is $\Pi^o=(1+\theta)/8$, and $\pi_s^*<\Pi^o$;
--   4. with the buy-back contract $b=w=1/2$ the competitive total order is $\theta/2$ and the supplier's expected profit $wq-\tfrac12b(q-s_l)-\tfrac12b(q-s_h)$ equals $\Pi^o$.
--
--   The wholesale price contract cannot prevent destructive competition in the low demand state; a full-refund buy-back does, and the supplier captures the integrated profit.
--
--   **Formalization Note** Perfect competition is the first zero of the retailers' aggregate expected profit; the continuum of retailers enters only through the total order. At $\theta=3$ both $w=1/2$ and $w=1/4$ are optimal and only the value is asserted as the maximum.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, pp. 55 (π_s(w*(θ)) and 'No matter the value of θ, π_s(w*(θ)) < Π°') and 57 (buy-back with full refund)

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, pp. 54–57. With wholesale price contracts the supplier's best profit is
`θ/(2(1+θ))` if `θ ≤ 3` and `θ/8` otherwise, attained at `w*(θ)`; it is strictly below the
monopolist's `Π° = (1 + θ)/8`; and with the full-refund buy-back `b = w = 1/2` the competitive
retailers order `θ/2` and the supplier earns `Π°`. -/
theorem sec_6_5_2_wholesale_vs_buyback (θ : ℝ) (hθ : 1 < θ) :
    IsGreatest (wholesaleOutcomes θ) (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) ∧
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    (∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      wStar θ * q = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8)) ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) ∧
    (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) < (1 + θ) / 8 ∧
    IsCompetitiveOrder (bbRetailerProfit θ (1 / 2) (1 / 2)) (θ / 2) ∧
    bbSupplierProfit θ (1 / 2) (1 / 2) (θ / 2) = (1 + θ) / 8 := by sorry

end CachonCoord.MarketClearing
