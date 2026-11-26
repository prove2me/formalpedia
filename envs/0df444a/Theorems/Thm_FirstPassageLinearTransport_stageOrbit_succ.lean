-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageOrbit_succ
-- name    : FirstPassageLinearTransport.stageOrbit_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:22:47.97802+00:00
-- url     : https://prove2.me/theorems/250e0614-2825-5205-8729-e70121a03fde
-- title:
--   First Passage Linear Transport: stage Orbit succ
-- statement:
--   The First Passage Linear Transport construction uses the stage Orbit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L220-L221
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L220-L221

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageOrbit_succ {r eta : ℝ} (p : StageSetup r eta) (R n : ℕ) :
    stageOrbit p (R + 1) n = stageOrbit p R (stageMap p n) := by sorry
