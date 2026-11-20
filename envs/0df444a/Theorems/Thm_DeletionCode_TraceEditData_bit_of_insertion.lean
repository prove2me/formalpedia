-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_bit_of_insertion
-- name    : DeletionCode.TraceEditData.bit_of_insertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:55.366516+00:00
-- url     : https://prove2.me/theorems/25453678-fd6c-4430-9ddb-0fac4bb3d119
-- title:
--   Trace Edit Data: bit of insertion
-- statement:
--   The Trace Edit Data construction uses the bit of insertion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L62-L63
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L62-L63

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.bit_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : bit trace c = b := by sorry
