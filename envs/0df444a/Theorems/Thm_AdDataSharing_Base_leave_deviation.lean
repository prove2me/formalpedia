-- Prove2me | Theorems.Thm_AdDataSharing_Base_leave_deviation
-- name    : AdDataSharing.Base.leave_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:01.41983+00:00
-- url     : https://prove2.me/theorems/e4632345-4def-4b6b-a1a7-9bff05fdf143
-- title:
--   §1.2, pp. 8–9 — leaving to ADX2 without cross-targeting earns (4), unprofitable iff (No Leave)
-- statement:
--   Assume the standing assumptions and suppose $ADX_1$ allows cross-targeting. Start from full cross-targeting, where each advertiser earns $(1+\eta_2)(C-w)$, display (2). If advertiser $A_i$ deviates to $ADX_2$ and does not cross-target ("leave"), it earns
--   $$
--   \alpha M+(1-2\alpha)C-(1-\alpha)w+\eta_1(C-w), \tag{4}
--   $$
--   and (4) $\le$ (2) holds if and only if
--   $$
--   \alpha(M-C)\le\alpha(C-w)+(\eta_2-\eta_1)(C-w). \quad\text{(No Leave)}
--   $$
--
--   This is the second of the two conditions that make full cross-targeting an equilibrium (Lemma 2).
--
--   **Formalization Note.** The payoffs do not depend on the snipe decisions of advertisers on $ADX_1$; the statement holds for all of them.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), pp. 8–9, §1.2, display (4) and comparing (4) to (2), (No Leave)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- §1.2, pp. 8–9, comparing (4) to (2): from full cross-targeting, the deviation to ADX2
without cross-targeting ("leave") earns (4), and it is not profitable if and only if
(No Leave) holds. -/
theorem leave_deviation (P : Params) (hP : P.Standing) (s s' : Bool) :
    payoffOpen P ⟨.adx2, false⟩ ⟨.adx1, s⟩ =
        P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w + P.η₁ * (P.C - P.w) ∧
      payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) ∧
      (payoffOpen P ⟨.adx2, false⟩ ⟨.adx1, s⟩ ≤ payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ ↔
        NoLeave P) := by sorry

end AdDataSharing.Base
