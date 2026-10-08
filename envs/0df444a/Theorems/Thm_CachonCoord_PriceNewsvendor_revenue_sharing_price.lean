-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_revenue_sharing_price
-- name    : CachonCoord.PriceNewsvendor.revenue_sharing_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:27.352091+00:00
-- url     : https://prove2.me/theorems/72448b1d-d47d-4d39-91a1-08150a241786
-- title:
--   §6.3.1, p. 36 — revenue sharing preserves price maximizers when goodwill is zero
-- statement:
--   When $g_r=g_s=0$, fix any order quantity $q\ge0$, any wholesale price $w_r$, and a positive revenue share $\phi$. If sales have price derivative $S_p(q,p)$ at an admissible price $p$, the chain and retailer price derivatives are
--
--   $$\Pi_p(q,p)=S(q,p)+(p-v)S_p(q,p),\qquad (\pi_r)_p(q,p)=\phi\Pi_p(q,p).$$
--
--   For fixed $q$, the set of admissible prices maximizing the retailer's profit is exactly the set maximizing integrated profit. This is the revenue-sharing price-coordination claim used in §6.3.1.
--
--   **Formalization Note** The printed display on p. 36 omits the factor $\phi$ in the derivative equality. It is restored here. Positivity of $\phi$ is needed to preserve maximizers; $\phi=0$ makes the retailer indifferent among prices.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, Eq. (17) and following display, p. 36

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- On p. 36 the printed equality of price derivatives omits the factor `φ`.
With no goodwill penalty and `φ > 0`, revenue sharing has exactly the chain's
price maximizers for each fixed quantity. -/
theorem revenue_sharing_price (M : Model) (q p phi wr Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0) (hphi : 0 < phi)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) :
    HasDerivAt (fun t => M.Pi q t) (M.S q p + (p - M.v) * Sp) p ∧
    HasDerivAt (fun t => M.revenueRetailer wr phi q t)
      (phi * (M.S q p + (p - M.v) * Sp)) p ∧
    (IsMaxOn (fun t => M.Pi q t) M.demand.prices p ↔
     IsMaxOn (fun t => M.revenueRetailer wr phi q t) M.demand.prices p) := by sorry

end CachonCoord.PriceNewsvendor
