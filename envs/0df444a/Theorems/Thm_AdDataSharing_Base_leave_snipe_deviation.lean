-- Prove2me | Theorems.Thm_AdDataSharing_Base_leave_snipe_deviation
-- name    : AdDataSharing.Base.leave_snipe_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:00.874162+00:00
-- url     : https://prove2.me/theorems/b0caae5b-4401-4e3b-a665-56dbe75152f8
-- title:
--   §1.2, p. 8 — leaving to ADX2 while cross-targeting earns (3), unprofitable iff (No Leave & Snipe)
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ allows cross-targeting. Start from full cross-targeting, where both advertisers share data with $ADX_1$ and each earns
--   $$
--   (1+\eta_2)(C-w). \tag{2}
--   $$
--   If advertiser $A_i$ deviates to $ADX_2$ but continues to cross-target its rival on $ADX_1$ ("leave and snipe"), it earns
--   $$
--   \alpha M+(1-\alpha)C-2(1-\alpha)w+\eta_1(C-w), \tag{3}
--   $$
--   and (3) $\le$ (2) holds if and only if
--   $$
--   \alpha(M-C)\le(1-2\alpha)w+(\eta_2-\eta_1)(C-w). \quad\text{(No Leave \& Snipe)}
--   $$
--
--   This is one of the two conditions that make full cross-targeting an equilibrium (Lemma 2).
--
--   **Formalization Note.** The payoffs do not depend on the snipe decisions of advertisers on $ADX_1$; the statement holds for all of them.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 8, §1.2, display (3) and comparing (3) to (2), (No Leave & Snipe)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- §1.2, p. 8, comparing (3) to (2): from full cross-targeting, the deviation to ADX2
while still cross-targeting the rival ("leave and snipe") earns (3), and it is not profitable
if and only if (No Leave & Snipe) holds. -/
theorem leave_snipe_deviation (P : Params) (hP : P.Standing) (s s' : Bool) :
    payoffOpen P ⟨.adx2, true⟩ ⟨.adx1, s⟩ =
        P.α * P.M + (1 - P.α) * P.C - 2 * (1 - P.α) * P.w + P.η₁ * (P.C - P.w) ∧
      payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) ∧
      (payoffOpen P ⟨.adx2, true⟩ ⟨.adx1, s⟩ ≤ payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ ↔
        NoLeaveSnipe P) := by sorry

end AdDataSharing.Base
