-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p57_rpm_order
-- name    : CachonCoord.MarketClearing.p57_rpm_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:53:28.296045+00:00
-- url     : https://prove2.me/theorems/a835778d-9bcf-4288-b5e1-9e35a2555c76
-- title:
--   §6.5.2, p. 57 — with (p̄, w̄) the retailers order θ/2 and the supplier earns Π°
-- statement:
--   Let $\theta>1$, $\bar p=1/2$ and $\bar w=\frac{1+\theta}{4\theta}$, with proportional allocation.
--   1. If the total order is $1/2<q<\theta/2$, a retailer holding $q(t)$ units at wholesale price $w$ earns $-q(t)w+\frac12\big(\frac{1/2}{q}q(t)\big)\bar p+\frac12q(t)\big(1-\frac q\theta\big)$.
--   2. For $q(t)>0$ this profit is strictly decreasing in the total order $q$ on $(1/2,\theta/2]$.
--   3. Under $(\bar p,\bar w)$ the competitive total order is $\theta/2$ (aggregate profit positive below $\theta/2$ and zero at $\theta/2$).
--   4. The supplier then earns $\bar w\cdot\theta/2=(1+\theta)/8=\Pi^o$.
--
--   Resale price maintenance thus restores the integrated profit.
--
--   **Formalization Note** Footnote 26 notes infinitely many individual equilibria $q(t)$; only the total order is stated.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 57, first paragraph

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 57: under resale price maintenance with `p̄ = 1/2`, for a total order `1/2 < q < θ/2` a
retailer holding `q(t)` units earns `−q(t)w + (1/2)(((1/2)/q)q(t))p̄ + (1/2)q(t)(1 − q/θ)`; this is
strictly decreasing in `q` up to `θ/2`; with `w̄ = (1 + θ)/(4θ)` the competitive total order is
`θ/2`, and the supplier earns `w̄ · θ/2 = (1 + θ)/8 = Π°`. -/
theorem p57_rpm_order (θ : ℝ) (hθ : 1 < θ) :
    (∀ w Q y : ℝ, 1 / 2 < Q → Q < θ / 2 →
      rpmRetailerProfit θ (1 / 2) w Q y =
        -y * w + (1 / 2) * (((1 / 2) / Q) * y) * (1 / 2) + (1 / 2) * y * (1 - Q / θ)) ∧
    (∀ w y : ℝ, 0 < y →
      StrictAntiOn (fun Q => rpmRetailerProfit θ (1 / 2) w Q y) (Set.Ioc (1 / 2) (θ / 2))) ∧
    IsCompetitiveOrder (fun Q => rpmRetailerProfit θ (1 / 2) ((1 + θ) / (4 * θ)) Q Q) (θ / 2) ∧
    (1 + θ) / (4 * θ) * (θ / 2) = (1 + θ) / 8 := by sorry

end CachonCoord.MarketClearing
