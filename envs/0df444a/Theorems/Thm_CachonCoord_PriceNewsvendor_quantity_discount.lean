-- Prove2me | Theorems.Thm_CachonCoord_PriceNewsvendor_quantity_discount
-- name    : CachonCoord.PriceNewsvendor.quantity_discount
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:30:49.094358+00:00
-- url     : https://prove2.me/theorems/2109884f-dbc5-4e04-a496-99641251e5e9
-- title:
--   §6.3.1, pp. 37–38 — the quantity discount w_d(q) keeps the price undistorted when g_s = 0 and makes q° optimal at p°
-- statement:
--   Let $(q^\circ,p^\circ)$ be an optimal feasible quantity-price pair of the integrated channel, and let $\lambda\in[0,1]$. Consider the quantity-discount schedule designed at $p^\circ$,
--
--   $$w_d(q)=\bigl((1-\lambda)(p^\circ-v+g)-g_s\bigr)\frac{S(q,p^\circ)}{q}+\lambda(c-v)-c_r+v,$$
--
--   under which the retailer earns $\pi_r(q,w_d(q),p)=(p-v+g_r)S(q,p)-(w_d(q)+c_r-v)q-g_r\mu(p)$. Then:
--
--   1. for every $q\ge0$ and admissible $p$, $\pi_r(q,w_d(q),p)=(p-v+g_r)S(q,p)-\lambda(c-v)q-g_r\mu(p)-\bigl((1-\lambda)(p^\circ-v+g)-g_s\bigr)S(q,p^\circ)$;
--   2. for every $q\ge0$, $\pi_r(q,w_d(q),p^\circ)=\lambda\bigl(\Pi(q,p^\circ)+g\mu(p^\circ)\bigr)-g_r\mu(p^\circ)$;
--   3. if $g_s=0$, then for every $q\ge0$ the admissible prices that maximize $\pi_r(q,w_d(q),\cdot)$ are exactly those that maximize $\Pi(q,\cdot)$;
--   4. given the price $p^\circ$, the quantity $q^\circ$ maximizes over $q\ge0$ both the retailer's profit $\pi_r(q,w_d(q),p^\circ)$ and the supplier's profit $\pi_s(q,w_d(q),p^\circ)=g_sS(q,p^\circ)+(w_d(q)-c_s)q-g_s\mu(p^\circ)$.
--
--   The quantity discount leaves all revenue with the retailer, so it does not distort the pricing decision when $g_s=0$, and it coordinates the quantity decision once $p^\circ$ is chosen.
--
--   **Formalization Note** The page's display for $\pi_r(q,w_d(q),p^\circ)$ omits the factor $\lambda$ in front of $\Pi(q,p^\circ)+g\mu$; it is restored in item 2. The page writes the price-derivative equality $\partial\pi_r/\partial p=\partial\Pi/\partial p$ (with its terms swapped on p. 37); item 3 states its consequence, equality of the price maximizers, which holds because $\pi_r-\Pi$ does not depend on $p$ when $g_s=0$, even with a price-dependent mean. The page shows that $p^\circ(q)$ is optimal for each $q$ and that $q^\circ$ is optimal given $p^\circ$; it does not claim that $(q^\circ,p^\circ)$ jointly maximizes the retailer's profit, and neither does this statement. At $q=0$ the junk value $w_d(0)$ is multiplied by $q=0$, and $S(0,p)=0$ for nonnegative demand.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.3.1, quantity-discount displays, pp. 37–38

import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The quantity discount of pp. 37–38, designed at the price component `p°` of an integrated
optimum `(q°, p°)`. (1) The retailer's profit identity of p. 38. (2) At `p = p°` the retailer
earns `λ(Π(q, p°) + gμ(p°)) - g_r μ(p°)` (the page's display omits the factor `λ`).
(3) If `g_s = 0`, for every `q` the retailer's optimal prices are exactly the chain's.
(4) Given `p°`, `q°` is optimal for the retailer and for the supplier. Joint optimality of
`(q°, p°)` for the retailer is not claimed (the page does not claim it). -/
theorem quantity_discount (M : Model) (lam : ℝ) (opt : ℝ × ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hopt_feasible : opt ∈ M.feasible)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) M.feasible opt) :
    (∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      M.qdRetailer lam opt.2 q p =
        (p - M.v + M.gr) * M.S q p - lam * (M.c - M.v) * q - M.gr * M.mu p -
          ((1 - lam) * (opt.2 - M.v + M.g) - M.gs) * M.S q opt.2) ∧
    (∀ q : ℝ, 0 ≤ q →
      M.qdRetailer lam opt.2 q opt.2 =
        lam * (M.Pi q opt.2 + M.g * M.mu opt.2) - M.gr * M.mu opt.2) ∧
    (M.gs = 0 → ∀ q : ℝ, 0 ≤ q → ∀ p ∈ M.demand.prices,
      (IsMaxOn (fun t => M.qdRetailer lam opt.2 q t) M.demand.prices p ↔
        IsMaxOn (fun t => M.Pi q t) M.demand.prices p)) ∧
    IsMaxOn (fun q => M.qdRetailer lam opt.2 q opt.2) (Set.Ici 0) opt.1 ∧
    IsMaxOn (fun q => M.qdSupplier lam opt.2 q opt.2) (Set.Ici 0) opt.1 := by sorry

end CachonCoord.PriceNewsvendor
