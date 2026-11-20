-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_bit_of_deletion
-- name    : DeletionCode.TraceEditData.bit_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:47.534005+00:00
-- url     : https://prove2.me/theorems/582ecbb8-df17-4543-88c5-54ca03f45fde
-- title:
--   Trace Edit Data: bit of deletion
-- statement:
--   The Trace Edit Data construction uses the bit of deletion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L59-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L59-L60

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.bit_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : bit trace c = b := by sorry
