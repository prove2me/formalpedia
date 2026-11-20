-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_matchedAnchor_mono
-- name    : DeletionCode.TraceSeparation.matchedAnchor_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:26.403911+00:00
-- url     : https://prove2.me/theorems/957b7a7e-0102-43f7-b270-42860d850024
-- title:
--   Trace Separation: matched Anchor mono
-- statement:
--   The Trace Separation construction uses the matched Anchor mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L38-L40
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L38-L40

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.matchedAnchor_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.matchedAnchor i ≤ trace.matchedAnchor j := by sorry
