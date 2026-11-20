-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_countP_isDeletion
-- name    : DeletionCode.TraceEditData.countP_isDeletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:57.995069+00:00
-- url     : https://prove2.me/theorems/15593967-d4c5-4be1-a7d7-cfb79308b4e9
-- title:
--   Trace Edit Data: count P is Deletion
-- statement:
--   The Trace Edit Data construction uses the count P is Deletion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L124-L128
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L124-L128

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.countP_isDeletion (trace : Trace) : trace.countP isDeletion = trace.deletions := by sorry
