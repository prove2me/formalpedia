-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_transportGap_pos
-- name    : FirstPassageLinearTransport.transportGap_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:13.238623+00:00
-- url     : https://prove2.me/theorems/b984ee23-d5d0-446b-b6a8-f4d378197cf7
-- title:
--   First Passage Linear Transport: transport Gap pos
-- statement:
--   The First Passage Linear Transport construction uses the transport Gap pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L384-L387
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L384-L387

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.transportGap_pos {r chi : ℝ} (hchi : chi < r) :
    0 < transportGap r chi := by sorry
