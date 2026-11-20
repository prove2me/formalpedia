-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_countP_isInsertion
-- name    : DeletionCode.TraceEditData.countP_isInsertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:43.67398+00:00
-- url     : https://prove2.me/theorems/9b6e2eb2-0413-44ec-8274-97e272ba849f
-- title:
--   Trace Edit Data: count P is Insertion
-- statement:
--   The Trace Edit Data construction uses the count P is Insertion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L130-L134
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L130-L134

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.countP_isInsertion (trace : Trace) : trace.countP isInsertion = trace.insertions := by sorry
