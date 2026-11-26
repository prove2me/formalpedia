-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rank_transport_multiplier_le
-- name    : FirstPassageLinearTransport.rank_transport_multiplier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:22.191632+00:00
-- url     : https://prove2.me/theorems/629a3c25-7be5-58fd-92b9-4044150bc3c8
-- title:
--   First Passage Linear Transport: rank transport multiplier le
-- statement:
--   The rank-scaled transport multiplier is bounded by one linear factor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L37-L56
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L37-L56

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.rank_transport_multiplier_le
    {r : ℝ} (hr : 0 < r) (q : ℕ) :
    1 + 3 * (((q + 2 : ℕ) : ℝ) / r) ≤
      (1 + 6 / r) * ((q + 1 : ℕ) : ℝ) := by sorry
