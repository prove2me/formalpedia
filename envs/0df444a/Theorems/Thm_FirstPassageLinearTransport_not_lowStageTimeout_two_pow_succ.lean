-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_not_lowStageTimeout_two_pow_succ
-- name    : FirstPassageLinearTransport.not_lowStageTimeout_two_pow_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:38:51.378789+00:00
-- url     : https://prove2.me/theorems/6ac8b274-e23d-5a93-a502-8446bdec3972
-- title:
--   First Passage Linear Transport: not low Stage Timeout two pow succ
-- statement:
--   The upper endpoint `2^(m+1)` of a landing band cannot time out once the
--   next target rank is positive: repeated halving reaches that target before
--   the deadline `m`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L185-L203
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L185-L203

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology

theorem FirstPassageLinearTransport.not_lowStageTimeout_two_pow_succ
    {K₀ : ℝ} {L m : ℕ}
    (hqpos : 0 < timeoutTargetRank K₀ L m)
    (hqlt : timeoutTargetRank K₀ L m < m + 1) :
    ¬LowStageTimeout K₀ L m (2 ^ (m + 1)) := by sorry
