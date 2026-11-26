-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
-- name    : FirstPassageLinearTransport.stageClock_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:13:16.830515+00:00
-- url     : https://prove2.me/theorems/295aab94-91f9-5b4c-b5be-1242b1009d5f
-- title:
--   First Passage Linear Transport: stage Clock succ
-- statement:
--   The First Passage Linear Transport construction uses the stage Clock succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L226-L228
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L226-L228

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageClock_succ {r eta : ℝ} (p : StageSetup r eta) (R n : ℕ) :
    stageClock p (R + 1) n =
      stageLength p n + stageClock p R (stageMap p n) := by sorry
