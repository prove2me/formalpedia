-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_deletions_take_mono
-- name    : DeletionCode.TraceSeparation.deletions_take_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:07.874302+00:00
-- url     : https://prove2.me/theorems/ab46590f-cad0-4053-9a5e-1cfce6bb2e2b
-- title:
--   Trace Separation: deletions take mono
-- statement:
--   The Trace Separation construction uses the deletions take mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L30-L32
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L30-L32

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.deletions_take_mono (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.deletions (trace.take i) ≤ Trace.deletions (trace.take j) := by sorry
