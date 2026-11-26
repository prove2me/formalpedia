-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_terminalTailPrefactor_pos
-- name    : FirstPassageLinearTransport.terminalTailPrefactor_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:06.060362+00:00
-- url     : https://prove2.me/theorems/2bdb8bc9-fcfb-5adc-9dd4-28a5027c799c
-- title:
--   First Passage Linear Transport: terminal Tail Prefactor pos
-- statement:
--   The First Passage Linear Transport construction uses the terminal Tail Prefactor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L41-L49
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L41-L49

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.terminalTailPrefactor_pos
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    0 < terminalTailPrefactor b b' c' := by sorry
