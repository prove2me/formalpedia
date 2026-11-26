-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
-- name    : FirstPassageLinearTransport.pullbackShellConstant_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:05:01.699306+00:00
-- url     : https://prove2.me/theorems/6b35c7e4-c9b7-53c9-9b73-ff5ee96e5062
-- title:
--   First Passage Linear Transport: pullback Shell Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the pullback Shell Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L512-L519
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L512-L519

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.pullbackShellConstant_pos {r eta chi Dc : ℝ}
    (p : StageSetup r eta) (hchi : chi < r) :
    0 < pullbackShellConstant p chi Dc := by sorry
