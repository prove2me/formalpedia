-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
-- name    : FirstPassageLinearTransport.bootstrapSet_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:49.773889+00:00
-- url     : https://prove2.me/theorems/ff84d373-76a8-4b18-9eed-2554f0de61d5
-- title:
--   First Passage Linear Transport: bootstrap Set succ
-- statement:
--   The First Passage Linear Transport construction uses the bootstrap Set succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L32-L33
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L32-L33

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.bootstrapSet_succ {r eta : ℝ} (p : StageSetup r eta) (R : ℕ) :
    bootstrapSet p (R + 1) = firstPassagePullback p (bootstrapSet p R) := by sorry
