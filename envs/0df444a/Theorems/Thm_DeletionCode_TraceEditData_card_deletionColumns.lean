-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_card_deletionColumns
-- name    : DeletionCode.TraceEditData.card_deletionColumns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:03.131921+00:00
-- url     : https://prove2.me/theorems/f7828e3e-6c59-49db-9773-f411d888bc4b
-- title:
--   Trace Edit Data: card deletion Columns
-- statement:
--   The Trace Edit Data construction uses the card deletion Columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L167-L170
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L167-L170

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.card_deletionColumns (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .deletion} = trace.deletions := by sorry
