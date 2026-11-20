-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_card_insertionColumns
-- name    : DeletionCode.TraceEditData.card_insertionColumns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:00.442535+00:00
-- url     : https://prove2.me/theorems/0b6b1f1c-fd4b-4948-9393-fb63a801ae88
-- title:
--   Trace Edit Data: card insertion Columns
-- statement:
--   The Trace Edit Data construction uses the card insertion Columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L172-L175
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L172-L175

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.card_insertionColumns (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .insertion} = trace.insertions := by sorry
