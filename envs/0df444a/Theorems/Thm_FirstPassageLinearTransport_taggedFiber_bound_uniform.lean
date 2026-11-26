-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_taggedFiber_bound_uniform
-- name    : FirstPassageLinearTransport.taggedFiber_bound_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:16.347173+00:00
-- url     : https://prove2.me/theorems/92f9c928-ce64-55ba-8c55-e576cbbe4462
-- title:
--   First Passage Linear Transport: tagged Fiber bound uniform
-- statement:
--   A tagged first-passage fiber has uniformly bounded cardinality.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L18-L86
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L18-L86

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.taggedFiber_bound_uniform {M Y H h y : ℕ}
    (hY : 0 < Y) (hpos : 1 ≤ h) (hhH : h ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by sorry
