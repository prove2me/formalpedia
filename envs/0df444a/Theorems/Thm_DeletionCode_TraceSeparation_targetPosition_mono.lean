-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_mono
-- name    : DeletionCode.TraceSeparation.targetPosition_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:13.355174+00:00
-- url     : https://prove2.me/theorems/8f6741b0-7d6b-400b-ada2-4cecfd3ea1ad
-- title:
--   Trace Separation: target Position mono
-- statement:
--   The Trace Separation construction uses the target Position mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L66-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L66-L70

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.targetPosition_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.targetPosition i ≤ trace.targetPosition j := by sorry
