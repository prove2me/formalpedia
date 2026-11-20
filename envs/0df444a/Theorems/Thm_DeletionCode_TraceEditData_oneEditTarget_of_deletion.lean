-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_of_deletion
-- name    : DeletionCode.TraceEditData.oneEditTarget_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:36.509415+00:00
-- url     : https://prove2.me/theorems/93988bf0-3073-45c7-bc4e-0040e1f5b3a0
-- title:
--   Trace Edit Data: one Edit Target of deletion
-- statement:
--   The Trace Edit Data construction uses the one Edit Target of deletion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L73-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L73-L76

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.oneEditTarget_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = trace.source.eraseIdx (position trace c) := by sorry
