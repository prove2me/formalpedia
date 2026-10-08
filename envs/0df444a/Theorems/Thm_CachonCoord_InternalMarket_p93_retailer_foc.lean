-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_p93_retailer_foc
-- name    : CachonCoord.InternalMarket.p93_retailer_foc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:42.823895+00:00
-- url     : https://prove2.me/theorems/4079c6dc-2f32-4e6c-bd2b-4c787957dfdd
-- title:
--   §6.9.1, p. 93 — retailer i's optimal quantity q*_i satisfies ((η−1)/η) α_i (q*_i)^{−1/η} − w = 0
-- statement:
--   Let $\eta>1$, $\alpha_i>0$ and a per-unit price $w>0$. Retailer $i$'s profit from $q_i\ge0$ units is $\pi_i(q_i,w)=\alpha_iq_i^{(\eta-1)/\eta}-wq_i$. Then:
--
--   1. for every $q_i>0$,
--   $$
--   \frac{\partial\pi_i(q_i,w)}{\partial q_i}=\Big(\frac{\eta-1}{\eta}\Big)\alpha_iq_i^{-1/\eta}-w;
--   $$
--   2. a quantity $q_i^*\ge0$ maximizes $\pi_i(\cdot,w)$ over $[0,\infty)$ if and only if $q_i^*>0$ and
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)\alpha_i(q_i^*)^{-1/\eta}-w=0.
--   $$
--
--   This is each retailer's demand curve in the internal market: it is used to compute what the retailers order at the price $w(\alpha,Q)$.
--
--   **Formalization Note** The page does not state $w>0$; it is needed, because for $w\le0$ the profit is unbounded and no optimal quantity exists. The price $w(\alpha,Q)$ at which the result is applied is positive.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 93, π_i(q_i, w) and the display after it

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 93, retailer `i`'s first-order condition (Cachon 2003, 3rd draft): with demand
realization `αᵢ > 0`, elasticity `η > 1` and per-unit price `w > 0`, the profit
`πᵢ(q, w) = αᵢ q^{(η−1)/η} − w q` has derivative `((η − 1)/η) αᵢ q^{−1/η} − w` at every `q > 0`, and a
quantity `q ≥ 0` maximizes `πᵢ(·, w)` over `[0, ∞)` if and only if `q > 0` and
`((η − 1)/η) αᵢ q^{−1/η} − w = 0`. -/
theorem p93_retailer_foc (η αᵢ w : ℝ) (hη : 1 < η) (hα : 0 < αᵢ) (hw : 0 < w) :
    (∀ q : ℝ, 0 < q →
      HasDerivAt (retailerProfit η αᵢ w) ((η - 1) / η * αᵢ * q ^ (-1 / η) - w) q) ∧
    ∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q ↔
        0 < q ∧ (η - 1) / η * αᵢ * q ^ (-1 / η) - w = 0) := by sorry

end CachonCoord.InternalMarket
