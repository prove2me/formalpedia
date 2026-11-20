-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_mono
-- name    : DeletionCode.TraceSeparation.sourcePosition_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:15.603906+00:00
-- url     : https://prove2.me/theorems/e931463a-de09-4bb9-b8ba-2672132aa778
-- title:
--   Trace Separation: source Position mono
-- statement:
--   The Trace Separation construction uses the source Position mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L60-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L60-L64

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.sourcePosition_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.sourcePosition i ≤ trace.sourcePosition j := by sorry
