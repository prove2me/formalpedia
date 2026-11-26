-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_terminalTailBound_polylog_le
-- name    : FirstPassageLinearTransport.terminalTailBound_polylog_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:21:33.261346+00:00
-- url     : https://prove2.me/theorems/cbafb2c1-41ca-4067-9e66-134c63e1f05c
-- title:
--   First Passage Linear Transport: terminal Tail Bound polylog le
-- statement:
--   Substitution of the terminal schedule gives the exact polynomial power
--   predicted by the paper calculation.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L98-L138
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L98-L138

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.terminalTailBound_polylog_le
    {A b b' c' : ℝ}
    (_hA : 0 < A)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (M : ℕ) :
    terminalTailBound b b' c' (polylogTerminalRank A M) ≤
      terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^
          (-(A * min b' c' / Real.log 2))) := by sorry
