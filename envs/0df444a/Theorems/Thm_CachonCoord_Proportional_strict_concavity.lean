-- Prove2me | Theorems.Thm_CachonCoord_Proportional_strict_concavity
-- name    : CachonCoord.Proportional.strict_concavity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:55.690073+00:00
-- url     : https://prove2.me/theorems/acf590e0-b3f1-4d3e-be3b-345b8db0420e
-- title:
--   p. 50 — each retailer's profit is strictly concave in his own order quantity
-- statement:
--   Under a buy-back contract with buy-back rate $b < p$ and any wholesale price $w$, and for any total stock $q_{-i} \ge 0$ of the other retailers, the function
--
--   $$
--   x \longmapsto \pi_i(x, q_{-i}) = (p-w)x - (p-b)\,\frac{x}{x+q_{-i}}\int_0^{x+q_{-i}}F(y)\,dy
--   $$
--
--   is strictly concave on $[0,\infty)$.
--
--   So each retailer has at most one best response to the others' orders, and a profile is a Nash equilibrium as soon as every interior order satisfies its first-order condition.
--
--   **Formalization Note** The book states the claim without conditions; $b < p$ is required (at $b = p$ the profit is linear in $x$) and is part of every contract the section considers ($b < w < p$). The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 50 ("The second order condition confirms each retailer's profit function is strictly concave in his order quantity")

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 50: "The second order condition confirms each retailer's profit function is strictly
concave in his order quantity." For a buy-back rate `b < p` and any total stock `s ≥ 0` of the
other retailers, `x ↦ π_i(x, s)` is strictly concave on `x ≥ 0`. -/
theorem strict_concavity (M : Model) (w b s : ℝ) (hb : b < M.p) (hs : 0 ≤ s) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x => M.retailerProfit w b x s) := by sorry

end CachonCoord.Proportional
