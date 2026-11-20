-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_insertions_take_mono
-- name    : DeletionCode.TraceSeparation.insertions_take_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:59.809861+00:00
-- url     : https://prove2.me/theorems/04f9ee9c-5c58-4e66-8819-cff2ac009b35
-- title:
--   Trace Separation: insertions take mono
-- statement:
--   The Trace Separation construction uses the insertions take mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L34-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L34-L36

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.insertions_take_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.insertions (trace.take i) ≤ Trace.insertions (trace.take j) := by sorry
