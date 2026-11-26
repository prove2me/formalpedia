-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weightedTailConstant_pos
-- name    : FirstPassageLinearTransport.weightedTailConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:19.912514+00:00
-- url     : https://prove2.me/theorems/caf393fd-332e-45fc-90dc-2ea124ab93a1
-- title:
--   First Passage Linear Transport: weighted Tail Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the weighted Tail Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L30-L39
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean#L30-L39

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.weightedTailConstant_pos
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) :
    0 < weightedTailConstant c c' := by sorry
