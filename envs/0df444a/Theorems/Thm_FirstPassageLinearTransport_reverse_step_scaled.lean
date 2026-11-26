-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverse_step_scaled
-- name    : FirstPassageLinearTransport.reverse_step_scaled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:29.761827+00:00
-- url     : https://prove2.me/theorems/39bc1313-7427-4d1e-bb0f-4a49f3825576
-- title:
--   First Passage Linear Transport: reverse step scaled
-- statement:
--   Exact one-step reverse identity, cleared only of the power of three.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L69-L88
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L69-L88

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverse_step_scaled {n : ℕ} (hn : 0 < n) :
    (3 : ℚ) ^ (n % 2) * (n : ℚ) =
      2 * (shortcut n : ℚ) *
        (if n % 2 = 1 then reverseOddFactor (shortcut n) else 1) := by sorry
