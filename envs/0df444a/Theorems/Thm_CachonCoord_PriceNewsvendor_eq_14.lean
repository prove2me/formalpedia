-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_eq_14
-- name    : CachonCoord.PriceNewsvendor.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:29:54.552221+00:00
-- url     : https://prove2.me/theorems/2596afd7-2d51-489f-abca-d18d40e51057
-- title:
--   Eq. (14), p. 34 — necessary price first-order condition without goodwill penalties
-- statement:
--   Let $q\ge0$ be fixed, and let $p$ be an interior price that maximizes the integrated channel's profit over admissible prices. When both goodwill penalties vanish, suppose expected sales are differentiable in price, with derivative $S_p(q,p)$. Then the necessary price condition of Eq. (14) is
--
--   $$S(q,p)+(p-v)S_p(q,p)=0.$$
--
--   This is the price condition against which a contract's retailer incentive can be compared.
--
--   **Formalization Note** The page writes $p-v+g$, but its displayed derivative omits the derivative of the price-dependent mean $\mu(p)$. The statement uses $g_r=g_s=0$, a case explicitly analyzed on pp. 36–37, so the displayed first-order condition is valid without assuming a constant mean. The price lies in the open admissible set.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, Eq. (14), p. 34; zero-goodwill case, p. 36

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (14), p. 34, in the zero-goodwill regime in which `μ(p)` does not add a
price-derivative term. The chosen price is an interior price optimum at fixed quantity. -/
theorem eq_14 (M : Model) (q p Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hmax : IsMaxOn (fun t => M.Pi q t) M.demand.prices p) :
    M.S q p + (p - M.v) * Sp = 0 := by sorry

end CachonCoord.PriceNewsvendor
