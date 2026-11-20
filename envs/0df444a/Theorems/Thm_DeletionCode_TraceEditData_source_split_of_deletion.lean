-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_source_split_of_deletion
-- name    : DeletionCode.TraceEditData.source_split_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:44.264174+00:00
-- url     : https://prove2.me/theorems/43cf9be8-3e10-42e2-a477-8dbe9fdf74b1
-- title:
--   Trace Edit Data: source split of deletion
-- statement:
--   The Trace Edit Data construction uses the source split of deletion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L232-L235
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L232-L235

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.source_split_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    trace.source = sourcePrefix trace c ++ b :: sourceSuffix trace c := by sorry
