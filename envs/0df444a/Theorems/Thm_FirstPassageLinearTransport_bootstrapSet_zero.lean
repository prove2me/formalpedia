-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
-- name    : FirstPassageLinearTransport.bootstrapSet_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:46.0918+00:00
-- url     : https://prove2.me/theorems/20fead25-8eec-46be-9578-095665554f83
-- title:
--   First Passage Linear Transport: bootstrap Set zero
-- statement:
--   The First Passage Linear Transport construction uses the bootstrap Set zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L29-L30
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L29-L30

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.bootstrapSet_zero {r eta : ℝ} (p : StageSetup r eta) :
    bootstrapSet p 0 = extendedWindow p := by sorry

attribute [defeq] FirstPassageLinearTransport.bootstrapSet_zero
