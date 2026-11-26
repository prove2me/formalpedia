-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
-- name    : FirstPassageLinearTransport.stageClock_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:52.090395+00:00
-- url     : https://prove2.me/theorems/602d572f-c02a-4d75-9b98-b754b67feba7
-- title:
--   First Passage Linear Transport: stage Clock zero
-- statement:
--   The First Passage Linear Transport construction uses the stage Clock zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L223-L224
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L223-L224

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageClock_zero {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageClock p 0 n = 0 := by sorry

attribute [defeq] FirstPassageLinearTransport.stageClock_zero
