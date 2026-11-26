-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutShellBad_subset_terminalOddUpperShell
-- name    : FirstPassageLinearTransport.timeoutShellBad_subset_terminalOddUpperShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:01.654233+00:00
-- url     : https://prove2.me/theorems/f0b01af1-33e1-59bc-8e0e-c80ec6f13703
-- title:
--   First Passage Linear Transport: timeout Shell Bad subset terminal Odd Upper Shell
-- statement:
--   Every literal timeout lies in the exact terminal binomial upper tail.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L886-L897
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L886-L897

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutShellBad_subset_terminalOddUpperShell
    (K₀ : ℝ) (L m : ℕ) :
    timeoutShellBad K₀ L m ⊆
      terminalOddUpperShell m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by sorry
