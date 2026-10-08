-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_general_profit_split
-- name    : CachonCoord.PriceNewsvendor.general_profit_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:24.816282+00:00
-- url     : https://prove2.me/theorems/6ac0a2d2-790b-436c-b9ed-a9443fcd8690
-- title:
--   §6.3.1, p. 36 — contingent buy-back allocates profit with goodwill penalties
-- statement:
--   For the printed contingent buy-back terms at any sharing parameter $\lambda\in[0,1]$, feasible order quantity $q$ and admissible price $p$, the two firms' expected profits satisfy
--
--   $$\pi_r=\lambda\bigl(\Pi(q,p)+g\mu(p)\bigr)-g_r\mu(p),\qquad \pi_s=(1-\lambda)\Pi(q,p)-(\lambda g-g_r)\mu(p).$$
--
--   This records the general-goodwill allocation behind the zero-goodwill coordination theorem.
--
--   **Formalization Note** The demand mean is $\mu(p)$, computed separately at each price. The identities are algebraic; when $g_r$ and $g_s$ are nonzero they do not imply that an integrated price optimum is a retailer or supplier optimum, because $\mu(p)$ can vary with $p$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, contingent buy-back retailer-profit display, p. 36; supplier profit from the §6.2.3 split, p. 17

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 36 algebraic allocation for arbitrary goodwill penalties, with the
mean demand evaluated at the chosen retail price. -/
theorem general_profit_split (M : Model) (lam q p : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices) :
    M.buybackRetailer (M.contingentW lam p) (M.contingentB lam p) q p =
      lam * (M.Pi q p + M.g * M.mu p) - M.gr * M.mu p ∧
    M.buybackSupplier (M.contingentW lam p) (M.contingentB lam p) q p =
      (1 - lam) * M.Pi q p - (lam * M.g - M.gr) * M.mu p := by sorry

end CachonCoord.PriceNewsvendor
