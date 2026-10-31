-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A2
-- name    : CCPCollateral.Incentive.eq_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:18.479976+00:00
-- url     : https://prove2.me/theorems/2102463d-1cb7-4a38-a8c9-747b12aae643
-- title:
--   (A2), proof of Proposition 2, p. 45 — a member hedges iff (A_CCP − I − F)𝒫 ≥ (D − I − F) + X^g(I, F)
-- statement:
--   Under the standing assumptions, for every number $g$ of other members who hedge and every collateral pair $(I,F)$, a member weakly prefers hedging to risk-shifting,
--   $$V(r,g;I,F)\le V(s,g;I,F),$$
--   if and only if
--   $$(A_{CCP}-I-F)\,\mathcal P\ \ge\ (D-I-F)+X^g(I,F),$$
--   where $V$ is the member value (13), $X^g$ the loss-sharing cost (16) and $\mathcal P=(\mu_s-\mu_r)/(p_c(q_r-q_s))$ the pledgeability.
--
--   This is the individual incentive constraint from which every equilibrium statement of Proposition 2 is derived.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 1, (A2), p. 45

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A2), proof of Proposition 2, Step 1 (p. 45): when `g` of the other members hedge, a member
weakly prefers hedging iff `(A_CCP − I − F) 𝒫 ≥ (D − I − F) + X^g(I, F)`. -/
theorem eq_A2 (m : Params) (hm : Standing m) :
    ∀ (g : ℕ) (I F : ℝ),
      m.V Action.r g I F ≤ m.V Action.s g I F ↔
        m.D - I - F + m.X g I F ≤ (m.Accp - I - F) * m.pledge := by sorry

end CCPCollateral.Incentive
