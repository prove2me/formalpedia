-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_position_eq_sourcePrefix_length
-- name    : DeletionCode.TraceEditData.position_eq_sourcePrefix_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:58.145171+00:00
-- url     : https://prove2.me/theorems/a95404a5-afbb-4da3-80b4-e422ed884859
-- title:
--   Trace Edit Data: position eq source Prefix length
-- statement:
--   The Trace Edit Data construction uses the position eq source Prefix length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L197-L198
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L197-L198

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.position_eq_sourcePrefix_length (trace : Trace) (c : EditColumn trace) :
    position trace c = (sourcePrefix trace c).length := by sorry
