-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
-- name    : FirstPassageLinearTransport.stageOrbit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:48.033193+00:00
-- url     : https://prove2.me/theorems/2d0feee6-accb-4f1a-8f9f-49a1f6a29737
-- title:
--   First Passage Linear Transport: stage Orbit zero
-- statement:
--   The First Passage Linear Transport construction uses the stage Orbit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L217-L218
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L217-L218

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageOrbit_zero {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageOrbit p 0 n = n := by sorry

attribute [defeq] FirstPassageLinearTransport.stageOrbit_zero
