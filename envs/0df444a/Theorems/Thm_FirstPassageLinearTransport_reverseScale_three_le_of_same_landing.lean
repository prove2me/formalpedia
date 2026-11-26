-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseScale_three_le_of_same_landing
-- name    : FirstPassageLinearTransport.reverseScale_three_le_of_same_landing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:16.383098+00:00
-- url     : https://prove2.me/theorems/fe307235-f4de-5627-a0ad-5d1e551991e9
-- title:
--   First Passage Linear Transport: reverse Scale three le of same landing
-- statement:
--   The First Passage Linear Transport construction uses the reverse Scale three le of same landing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L269-L298
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L269-L298

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseScale_three_le_of_same_landing {n₁ n₂ h y : ℕ}
    (hy₁ : orbit h n₁ = y) (hy₂ : orbit h n₂ = y)
    (hs : oddCount n₁ h < oddCount n₂ h) :
    3 * reverseScale n₂ h ≤ reverseScale n₁ h := by sorry
