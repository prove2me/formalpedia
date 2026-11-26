-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcut_two_pow_succ
-- name    : FirstPassageLinearTransport.shortcut_two_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:46.804221+00:00
-- url     : https://prove2.me/theorems/9dff3fe8-2bda-5bcf-b2b2-f2eec48844ed
-- title:
--   First Passage Linear Transport: shortcut two pow succ
-- statement:
--   Shortcut iteration simply peels powers of two.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L160-L166
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L160-L166

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology

theorem FirstPassageLinearTransport.shortcut_two_pow_succ (k : ℕ) :
    shortcut (2 ^ (k + 1)) = 2 ^ k := by sorry
