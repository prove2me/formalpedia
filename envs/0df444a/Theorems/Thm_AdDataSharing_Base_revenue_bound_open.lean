-- Prove2me | Theorems.Thm_AdDataSharing_Base_revenue_bound_open
-- name    : AdDataSharing.Base.revenue_bound_open
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:22.02079+00:00
-- url     : https://prove2.me/theorems/c35be31e-1d48-4449-a6d1-5cd8d9d88e20
-- title:
--   Proof of Proposition 1, (15) — without full cross-targeting ADX1 earns at most 2wφ(1 − α + η₁) < (13)
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ allows cross-targeting. Then:
--   1. for every profile in which not both advertisers share data with $ADX_1$, its revenue is at most
--   $$
--   2w\varphi(1-\alpha+\eta_1); \tag{15}
--   $$
--   2. this bound is attained when one advertiser shares data with $ADX_1$ and the other, on $ADX_2$, cross-targets it on $ADX_1$;
--   3. the bound is strictly less than the closed revenue $2w\varphi(1-\alpha+\eta_2)$ of (13).
--
--   This gives the "only if" direction of Proposition 1: without full cross-targeting, opening is strictly worse for $ADX_1$.
--
--   **Formalization Note.** The bound holds for every such profile, not only equilibria, so no equilibrium hypothesis is needed.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 28, proof of Proposition 1, display (15)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Proof of Proposition 1, p. 28, display (15): if ADX1 is open and not both advertisers
contract with it, its revenue is at most `2wφ(1 − α + η₁)`; this bound is attained when one
advertiser contracts with ADX1 and the other cross-targets on ADX1; and it is strictly less than
(13). -/
theorem revenue_bound_open (P : Params) (hP : P.Standing) :
    (∀ σ : Plan × Plan, ¬ (σ.1.ex = .adx1 ∧ σ.2.ex = .adx1) →
        revenue P true σ ≤ 2 * P.w * P.φ * (1 - P.α + P.η₁)) ∧
      (∀ s : Bool, revenue P true (⟨.adx1, s⟩, ⟨.adx2, true⟩) = 2 * P.w * P.φ * (1 - P.α + P.η₁)) ∧
      2 * P.w * P.φ * (1 - P.α + P.η₁) < 2 * P.w * P.φ * (1 - P.α + P.η₂) := by sorry

end AdDataSharing.Base
