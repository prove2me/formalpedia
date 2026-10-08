-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_price_contingent_coordinates
-- name    : CachonCoord.PriceNewsvendor.price_contingent_coordinates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:57.066065+00:00
-- url     : https://prove2.me/theorems/1d86360d-50ea-4073-a746-ee930ea7cfa4
-- title:
--   §6.3.1, pp. 36–37 — contingent buy-back and revenue sharing coordinate price and quantity
-- statement:
--   Suppose both goodwill penalties vanish, and let $\lambda\in[0,1]$. Assume the integrated channel has an optimal feasible quantity-price pair $(q^\circ,p^\circ)$. For every feasible pair $(q,p)$, the printed price-contingent buy-back terms $b(p),w_b(p)$ and the coordinating revenue-sharing terms $\phi=\lambda$, $w_r=\lambda(c-v)-c_r+\lambda v$ give
--
--   $$\pi_r^{\mathrm{BB}}(q,p)=\pi_r^{\mathrm{RS}}(q,p)=\lambda\Pi(q,p),\qquad \pi_s^{\mathrm{BB}}(q,p)=(1-\lambda)\Pi(q,p).$$
--
--   Consequently $(q^\circ,p^\circ)$ maximizes both firms' profits under the contingent buy-back schedule. At $\lambda=0$ the retailer is indifferent, and at $\lambda=1$ the supplier is indifferent.
--
--   **Formalization Note** Expected sales and mean demand come from the price-indexed law; the mean may vary with $p$. The zero-goodwill restriction is necessary for the page's global optimality conclusion with such demand. The statement concerns profit schedules over $q\ge0$ and the admissible prices. Economic buy-back bounds such as $0\le b(p)\le w_b(p)$ require separate parameter checks.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, price-discount-sharing and revenue-sharing displays, pp. 35–37

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 36–37 price-contingent buyback is equivalent to coordinating
revenue sharing without goodwill penalties. Both firms attain their maximum
profit at every integrated optimum; an endpoint share may make one indifferent. -/
theorem price_contingent_coordinates (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ x : ℝ × ℝ, x ∈ M.feasible →
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.revenueRetailer (M.revenueW lam) lam x.1 x.2 =
        lam * M.Pi x.1 x.2 ∧
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2 =
        (1 - lam) * M.Pi x.1 x.2) ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackRetailer (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt ∧
    IsMaxOn (fun x : ℝ × ℝ =>
      M.buybackSupplier (M.contingentW lam x.2) (M.contingentB lam x.2) x.1 x.2)
      M.feasible opt := by sorry

end CachonCoord.PriceNewsvendor
