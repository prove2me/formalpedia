-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p43_quantity_discount_profit
-- name    : CachonCoord.EffortNewsvendor.p43_quantity_discount_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:08.637842+00:00
-- url     : https://prove2.me/theorems/11aff0fc-a545-48ed-85b6-5f601a054abc
-- title:
--   §6.4.1, p. 43 — under the quantity discount w_d the retailer earns π_r(q, e°) = λΠ(q, e°)
-- statement:
--   In the effort model of §6.4.1, let $e^o$ be an effort level and $\lambda \in [0, 1]$, and let the retailer pay $T_d(q) = w_d(q)q$ with the quantity discount schedule
--
--   $$
--   w_d(q) = (1 - \lambda)p\,\frac{S(q, e^o)}{q} + \lambda c - (1 - \lambda)\frac{g(e^o)}{q}.
--   $$
--
--   Then for every $q > 0$ and every effort $e$,
--
--   $$
--   \pi_r(q, e) = pS(q, e) - (1 - \lambda)pS(q, e^o) - \lambda cq - g(e) + (1 - \lambda)g(e^o),
--   $$
--
--   and in particular
--
--   $$
--   \pi_r(q, e^o) = \lambda pS(q, e^o) - \lambda cq - \lambda g(e^o) = \lambda \Pi(q, e^o).
--   $$
--
--   The retailer keeps all realized revenue and bears all of his effort cost, while his order is charged against expected revenue at $e^o$. This is why the quantity discount, alone among the section's contracts, aligns both decisions.
--
--   **Formalization Note** The sign of the $g(e^o)/q$ term is the one under which the page's two displays of $\pi_r$ hold; the page prints $+(1 - \lambda)g(e^o)/q$ (see the definition's note).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, p. 43, the schedule w_d(q) and the two displays of π_r

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 43, the two displays of `π_r`: under the quantity discount `w_d` with `λ ∈ [0, 1]`, for
every `q > 0` and every effort `e`,
`π_r(q, e) = pS(q, e) − (1 − λ)pS(q, e°) − λcq − g(e) + (1 − λ)g(e°)`, and at `e = e°`,
`π_r(q, e°) = λpS(q, e°) − λcq − λg(e°) = λΠ(q, e°)`. -/
theorem p43_quantity_discount_profit (M : Model) (lam eo q e : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hq : 0 < q) :
    M.qdRetailerProfit lam eo q e =
        M.p * M.S q e - (1 - lam) * M.p * M.S q eo - lam * M.c * q - M.effortCost e
          + (1 - lam) * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo =
        lam * M.p * M.S q eo - lam * M.c * q - lam * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo := by sorry

end CachonCoord.EffortNewsvendor
