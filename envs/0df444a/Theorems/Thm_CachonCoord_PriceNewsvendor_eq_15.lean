-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_eq_15
-- name    : CachonCoord.PriceNewsvendor.eq_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:06.830637+00:00
-- url     : https://prove2.me/theorems/23171f7e-fd0e-452f-98e6-8ab46c7acf56
-- title:
--   Eq. (15), p. 34 — quantity flexibility coordinates the price only if w_q = v − c_r or δ = 0
-- statement:
--   Assume both goodwill penalties vanish, $g_r=g_s=0$. Fix a quantity $q>0$ and a quantity-flexibility contract with wholesale price $w_q$ and flexibility $\delta\in[0,1]$, under which the retailer earns
--
--   $$\pi_r(q,p,w_q,\delta)=(p-v)S(q,p)-(w_q+c_r-v)q+(w_q+c_r-v)\int_{(1-\delta)q}^{q}F(y\mid p)\,dy.$$
--
--   Let $p$ be an admissible price that maximizes the integrated profit $\Pi(q,\cdot)$ and also the retailer's profit $\pi_r(q,\cdot,w_q,\delta)$. Suppose $S(q,\cdot)$ is differentiable at $p$, and that the price derivative of $\int_{(1-\delta)q}^{q}F(y\mid p)\,dy$ is $\int_{(1-\delta)q}^{q}\partial F(y\mid p)/\partial p\,dy$ with an integrable integrand. Then
--
--   $$w_q=v-c_r\quad\text{or}\quad\delta=0.$$
--
--   Since $w_q=v-c_r$ leaves the supplier with a negative margin and $\delta=0$ is a plain wholesale-price contract, the quantity-flexibility contract does not coordinate the newsvendor with price-dependent demand.
--
--   **Formalization Note** The page argues for general goodwill by comparing (15) with (14), but both displays differentiate $g\mu$ and $g_r\mu$ as constants, while $\mu(p)$ varies with the price under the section's assumption $\partial F(y\mid p)/\partial p>0$. The statement therefore takes the zero-goodwill case, where the page's conclusion "$g_s=0$ and either $w_q=v-c_r$ or $\delta=0$" reduces to the displayed disjunction. Differentiation under the integral sign and the integrability of $\partial F/\partial p$ on $[(1-\delta)q,q]$ are disclosed regularity hypotheses; $q>0$ and $\delta\le1$ keep the integration range inside $(0,\infty)$, where $\partial F/\partial p>0$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, Eqs. (14)–(15), p. 34

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (15) against (14), p. 34, in the zero-goodwill regime. If the quantity-flexibility
contract `(w_q, δ)`, `0 ≤ δ ≤ 1`, leaves an interior integrated-optimal price `p` (at fixed
`q > 0`) optimal for the retailer, then `w_q = v - c_r` or `δ = 0`. The price derivative of
`∫_{(1-δ)q}^q F(y|p) dy` is taken, as on the page, to be `∫_{(1-δ)q}^q ∂F(y|p)/∂p dy`
(differentiation under the integral sign, a disclosed regularity hypothesis). -/
theorem eq_15 (M : Model) (q p wq δ Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hFint : IntervalIntegrable (fun y => M.demand.priceSlope y p) MeasureTheory.volume
      ((1 - δ) * q) q)
    (hI : HasDerivAt (fun t => ∫ y in (1 - δ) * q..q, cdfOf (M.demand.law t) y)
      (∫ y in (1 - δ) * q..q, M.demand.priceSlope y p) p)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.qfRetailer wq δ q t) M.demand.prices p) :
    wq = M.v - M.cr ∨ δ = 0 := by sorry

end CachonCoord.PriceNewsvendor
