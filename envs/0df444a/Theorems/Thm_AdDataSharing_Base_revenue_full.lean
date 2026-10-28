-- Prove2me | Theorems.Thm_AdDataSharing_Base_revenue_full
-- name    : AdDataSharing.Base.revenue_full
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:08.995987+00:00
-- url     : https://prove2.me/theorems/a61e9c77-33e8-4547-9961-22b54958761f
-- title:
--   Proof of Proposition 1, (14) — under full cross-targeting ADX1 earns 2wφ(1 + η₂) > (13)
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ allows cross-targeting. Whenever both advertisers share data with $ADX_1$, its revenue is
--   $$
--   2w\varphi(1+\eta_2), \tag{14}
--   $$
--   and this is strictly larger than the closed revenue $2w\varphi(1-\alpha+\eta_2)$ of (13).
--
--   This gives the "if" direction of Proposition 1: when full cross-targeting is the selected continuation, opening is strictly better for $ADX_1$.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 28, proof of Proposition 1, display (14)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Proof of Proposition 1, p. 28, display (14): if ADX1 is open and both advertisers contract
with it, its revenue is `2wφ(1 + η₂)`, which is strictly higher than (13). -/
theorem revenue_full (P : Params) (hP : P.Standing) :
    (∀ σ : Plan × Plan, σ.1.ex = .adx1 → σ.2.ex = .adx1 →
        revenue P true σ = 2 * P.w * P.φ * (1 + P.η₂)) ∧
      2 * P.w * P.φ * (1 - P.α + P.η₂) < 2 * P.w * P.φ * (1 + P.η₂) := by sorry

end AdDataSharing.Base
