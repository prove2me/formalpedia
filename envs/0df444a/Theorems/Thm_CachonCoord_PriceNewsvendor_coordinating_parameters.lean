-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_coordinating_parameters
-- name    : CachonCoord.PriceNewsvendor.coordinating_parameters
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:24.472948+00:00
-- url     : https://prove2.me/theorems/c61eff6d-8567-440c-89d3-55e45bd83b59
-- title:
--   §6.3.1, p. 35 — price-contingent buy-back terms satisfy Eqs. (5) and (6)
-- statement:
--   Fix a sharing parameter $\lambda\in[0,1]$ and an admissible retail price $p$. Set the buy-back rate and wholesale price to the printed linear functions $b(p)$ and $w_b(p)$. They satisfy the two fixed-price coordination equations at that price:
--
--   $$p-v+g_r-b(p)=\lambda(p-v+g),\qquad w_b(p)-b(p)+c_r-v=\lambda(c-v).$$
--
--   These identities make the retailer's sales and order coefficients proportional to the integrated channel's coefficients at every retail price.
--
--   **Formalization Note** The functions $b(p)$ and $w_b(p)$ are the explicit formulas on p. 35. The statement does not define them by the desired profit identity. Their economic admissibility as buy-back terms must be checked separately for a selected cost and sharing parameter.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §§6.2.3, 6.3.1, Eqs. (5)–(6), pp. 17, 35

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 35 price-contingent terms satisfy the buyback coordination equations
(5) and (6) at each price. -/
theorem coordinating_parameters (M : Model) (lam p : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hp : p ∈ M.demand.prices) :
    p - M.v + M.gr - M.contingentB lam p = lam * (p - M.v + M.g) ∧
    M.contingentW lam p - M.contingentB lam p + M.cr - M.v =
      lam * (M.c - M.v) := by sorry

end CachonCoord.PriceNewsvendor
