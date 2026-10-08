-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p50_retailer_profit
-- name    : CachonCoord.Proportional.p50_retailer_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:53.856556+00:00
-- url     : https://prove2.me/theorems/497e68e8-f489-4742-9129-3314b640b746
-- title:
--   p. 50 — π_i(q_i, q_−i) = (p − w)q_i − (p − b)(q_i/q)∫₀^q F(x)dx
-- statement:
--   Let retailer $i$ order $q_i \ge 0$, let the other retailers order $q_{-i} \ge 0$ in total, and let $q = q_i + q_{-i}$. When total demand is allocated in proportion to stock, retailer $i$'s expected profit under a buy-back contract with wholesale price $w$ and buy-back rate $b$ is
--
--   $$
--   \pi_i(q_i, q_{-i}) = (p-w)q_i - (p-b)\,\frac{q_i}{q}\int_0^q F(x)\,dx .
--   $$
--
--   Setting $b = 0$ gives the retailer's profit under a wholesale-price contract. The closed form is what every later computation in the section differentiates.
--
--   **Formalization Note** The left side is the expectation defining $\pi_i$; when $q = 0$ both sides are $0$ (Lean's $0/0 = 0$ in the factor $q_i/q$ agrees with the retailer's actual profit $0$). The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 50 (display of π_i(q_i, q_−i))

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 50, display of `π_i`: with proportional allocation, retailer `i`'s expected profit
under a buy-back contract `(w, b)` is
`π_i(q_i, q_{−i}) = (p − w) q_i − (p − b) (q_i/q) ∫_0^q F(x) dx`, `q = q_i + q_{−i}`. -/
theorem p50_retailer_profit (M : Model) (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * ∫ y in (0 : ℝ)..(x + s), M.F y := by sorry

end CachonCoord.Proportional
