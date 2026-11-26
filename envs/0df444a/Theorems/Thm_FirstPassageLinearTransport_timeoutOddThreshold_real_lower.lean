-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutOddThreshold_real_lower
-- name    : FirstPassageLinearTransport.timeoutOddThreshold_real_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:37.68771+00:00
-- url     : https://prove2.me/theorems/4c23d4cd-6bd5-4400-8e6f-12dfb908cb42
-- title:
--   First Passage Linear Transport: timeout Odd Threshold real lower
-- statement:
--   The least integral timeout threshold differs from `q log₃ 2` by less
--   than one on the lower side.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L506-L529
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L506-L529

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutOddThreshold_real_lower (q : ℕ) :
    (q : ℝ) * logThreeTwo - 1 < (timeoutOddThreshold q : ℝ) := by sorry
