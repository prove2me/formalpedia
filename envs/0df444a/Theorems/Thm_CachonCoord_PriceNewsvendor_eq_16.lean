-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_eq_16
-- name    : CachonCoord.PriceNewsvendor.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:29:52.975296+00:00
-- url     : https://prove2.me/theorems/e61b6f45-bee5-4c5c-a777-f8c9b61829fe
-- title:
--   Eq. (16), p. 35 — a buy-back with fixed terms coordinates the price only if b = −g_s
-- statement:
--   Assume both goodwill penalties vanish, $g_r=g_s=0$. Fix a quantity $q\ge0$ and a buy-back contract with wholesale price $w_b$ and buy-back rate $b$, under which the retailer earns
--
--   $$\pi_r(q,p,w_b,b)=(p-v-b)S(q,p)-(w_b-b+c_r-v)q.$$
--
--   Let $p$ be an admissible price that maximizes both the integrated profit $\Pi(q,\cdot)$ and the retailer's profit $\pi_r(q,\cdot,w_b,b)$, and suppose $S(q,\cdot)$ has a nonzero derivative $\partial S(q,p)/\partial p$ at $p$. Then
--
--   $$b=-g_s,$$
--
--   and if, in addition, $(w_b,b)$ satisfies the coordination equations (5)–(6) of §6.2 for some $\lambda$, namely $p-v+g_r-b=\lambda(p-v+g)$ and $w_b-b+c_r-v=\lambda(c-v)$, then $w_b=c_s-g_s$, a wholesale price that leaves the supplier no margin. So a buy-back contract with fixed terms does not coordinate the newsvendor with price-dependent demand.
--
--   **Formalization Note** The page compares (16) with (14) for general goodwill, but both displays omit the price derivative of the mean demand $\mu(p)$, which varies with $p$ under the section's assumption $\partial F(y\mid p)/\partial p>0$. The statement takes the zero-goodwill case, in which both first-order conditions are exact; there $-g_s=0$. The nonzero derivative of expected sales is a hypothesis, as in the page's comparison.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, Eqs. (14) and (16), pp. 34–35

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (16) against (14), p. 35, in the zero-goodwill regime. If a buy-back contract
with fixed terms `(w_b, b)` leaves an interior integrated-optimal price `p` (at fixed `q`)
optimal for the retailer, and expected sales have a nonzero price derivative there, then
`b = -g_s`; moreover any `λ` for which `(w_b, b)` satisfies (5)–(6) forces `w_b = c_s - g_s`. -/
theorem eq_16 (M : Model) (q p wb b Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) (hSp : Sp ≠ 0)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.buybackRetailer wb b q t) M.demand.prices p) :
    b = -M.gs ∧
    ∀ lam : ℝ, p - M.v + M.gr - b = lam * (p - M.v + M.g) →
      wb - b + M.cr - M.v = lam * (M.c - M.v) → wb = M.cs - M.gs := by sorry

end CachonCoord.PriceNewsvendor
