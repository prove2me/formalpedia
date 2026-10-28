-- Prove2me | Theorems.Thm_AdDataSharing_Base_revenue_closed
-- name    : AdDataSharing.Base.revenue_closed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:02.314823+00:00
-- url     : https://prove2.me/theorems/a419e7a6-dbdb-4287-bb41-357b8f753f20
-- title:
--   Proof of Proposition 1, (13) — ADX1's revenue when closed is 2wφ(1 − α + η₂)
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ does not allow cross-targeting. In every subgame-perfect equilibrium of stages 2–3, $ADX_1$'s revenue is
--   $$
--   2w\varphi(1-\alpha+\eta_2). \tag{13}
--   $$
--
--   This is the value of the closed option that $ADX_1$ compares with opening.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 27, proof of Proposition 1, display (13)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Proof of Proposition 1, p. 27, display (13): if ADX1 is closed, its revenue in every
equilibrium of stages 2–3 is `2wφ(1 − α + η₂)`. -/
theorem revenue_closed (P : Params) (hP : P.Standing) (σ : Plan × Plan) (hσ : IsSPE P false σ) :
    revenue P false σ = 2 * P.w * P.φ * (1 - P.α + P.η₂) := by sorry

end AdDataSharing.Base
