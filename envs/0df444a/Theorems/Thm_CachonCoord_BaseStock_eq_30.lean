-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_30
-- name    : CachonCoord.BaseStock.eq_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:46:09.09915+00:00
-- url     : https://prove2.me/theorems/2fb7534f-0bbf-43eb-8d2b-36842f7de299
-- title:
--   Eq. (30), p. 73 — channel cost formula and strict convexity
-- statement:
--   In the single-location model, the retailer pays $h_r I_r(s)+\beta_r B_r(s)$ and the supplier pays $\beta_s B_r(s)$, where $\beta=\beta_r+\beta_s$ and $\mu_r=\mathbb E[D_r]$. For every real stock level $s$, their total cost is
--   $$c(s)=\beta(\mu_r-s)+(h_r+\beta)I_r(s).$$
--   The channel cost is strictly convex on $[0,\infty)$.
--
--   This cost function is the objective minimized by the integrated supply chain.
--
--   **Formalization Note** The page says "c(s_r) is strictly convex" without naming a domain. At negative levels the cost is affine (there $I_r = 0$ because demand is nonnegative), so the claim holds only on nonnegative levels and strict convexity is stated on $[0,\infty)$. The identity itself holds on all of $\mathbb R$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (30) and following sentence, p. 73

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (30) and following sentence, p. 73:
the channel cost formula and strict convexity for feasible nonnegative stock levels. -/
theorem eq_30 (M : Model) :
    (∀ s : ℝ, M.chainCost s =
      M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s) ∧
    StrictConvexOn ℝ (Set.Ici 0) M.chainCost := by sorry

end CachonCoord.BaseStock
