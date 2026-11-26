-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageK_pos
-- name    : FirstPassageLinearTransport.stageK_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:54.162801+00:00
-- url     : https://prove2.me/theorems/a247d115-2cbd-51c6-860c-7e182254f775
-- title:
--   First Passage Linear Transport: stage K pos
-- statement:
--   The First Passage Linear Transport construction uses the stage K pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L147-L148
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L147-L148

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageK_pos {r eta : ℝ} (p : StageSetup r eta) :
    0 < stageK p := by sorry
