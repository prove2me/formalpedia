-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
-- name    : FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:53.388598+00:00
-- url     : https://prove2.me/theorems/931ec970-5401-4f9a-afca-634712ac456b
-- title:
--   Stage Setup: lower Tolerance M0
-- statement:
--   The Stage Setup construction uses the lower Tolerance M0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L49-L52
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L49-L52

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
    {r eta : ℝ} (p : StageSetup r eta) (t : ℝ)
    (ht0 : 0 < t) (hteta : t ≤ eta) :
    (p.lowerTolerance t ht0 hteta).M0 = p.M0 := by sorry

attribute [defeq] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
