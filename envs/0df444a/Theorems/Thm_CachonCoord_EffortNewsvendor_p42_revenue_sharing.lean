-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p42_revenue_sharing
-- name    : CachonCoord.EffortNewsvendor.p42_revenue_sharing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:03.099635+00:00
-- url     : https://prove2.me/theorems/6a8a461f-c115-488f-a8e1-eb6fa245042a
-- title:
--   §6.4.1, p. 42 — with revenue sharing φ < 1 the retailer under-rewards effort: ∂π_r/∂e < ∂Π/∂e
-- statement:
--   In the effort model of §6.4.1, consider a revenue sharing contract with wholesale price $w_r$ under which the retailer keeps the fraction $\phi < 1$ of revenue. His profit is $\pi_r(q, e, w_r, \phi) = \phi p S(q, e) - w_r q - g(e)$. For every $q > 0$ and $e > 0$ both $\pi_r$ and $\Pi$ are differentiable in $e$, and
--
--   $$
--   \frac{\partial \pi_r(q, e, w_r, \phi)}{\partial e} < \frac{\partial \Pi(q, e)}{\partial e}.
--   $$
--
--   So the retailer's optimal effort is lower than the supply chain's.
--
--   **Formalization Note** The page does not display $\pi_r$ for revenue sharing in §6.4. The formalization uses §6.2.4's retailer profit (p. 21) with this section's zeros $v = g_r = c_r = 0$, less the effort cost $g(e)$. The book says only "it can be shown".
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, p. 42, the display after "It can be shown with φ < 1"; profit function from §6.2.4, p. 21

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 42, the display after "It can be shown with φ < 1": with a revenue sharing contract
`{w_r, φ}` and `φ < 1`, at every `q > 0` and `e > 0`,
`∂π_r(q, e, w_r, φ)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_revenue_sharing (M : Model) (wr φ q e : ℝ) (hφ : φ < 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.rsRetailerProfit wr φ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor
