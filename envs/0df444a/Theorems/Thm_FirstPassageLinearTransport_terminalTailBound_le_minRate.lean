-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_terminalTailBound_le_minRate
-- name    : FirstPassageLinearTransport.terminalTailBound_le_minRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:22.380933+00:00
-- url     : https://prove2.me/theorems/76e50ea9-7dcf-4941-b144-d448fefd8125
-- title:
--   First Passage Linear Transport: terminal Tail Bound le min Rate
-- statement:
--   The exact two-term terminal tail is bounded by one exponential at the
--   slower retained rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L53-L94
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L53-L94

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.terminalTailBound_le_minRate
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L : ℕ) :
    terminalTailBound b b' c' L ≤
      terminalTailPrefactor b b' c' *
        Real.exp (-(min b' c' * (L : ℝ))) := by sorry
