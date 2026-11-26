-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageMap_is_actual
-- name    : FirstPassageLinearTransport.stageMap_is_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:51.099545+00:00
-- url     : https://prove2.me/theorems/bc2ed70b-f72a-504e-b0a8-0bb8851603dd
-- title:
--   First Passage Linear Transport: stage Map is actual
-- statement:
--   The First Passage Linear Transport construction uses the stage Map is actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L92-L93
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L92-L93

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.stageMap_is_actual {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageMap p n = orbit (stageLength p n) n := by sorry
