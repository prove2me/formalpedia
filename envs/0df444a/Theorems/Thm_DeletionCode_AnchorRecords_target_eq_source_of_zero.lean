-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_target_eq_source_of_zero
-- name    : DeletionCode.AnchorRecords.target_eq_source_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:54:27.335178+00:00
-- url     : https://prove2.me/theorems/e4e41561-c66f-444e-a3b3-f89f7be16a3c
-- title:
--   Anchor Records: target eq source of zero
-- statement:
--   Zero deletions and insertions leave every source letter matched.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L114-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L114-L119

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.target_eq_source_of_zero (trace : Trace)
    (hdel : trace.deletions = 0) (hins : trace.insertions = 0) :
    trace.target = trace.source := by sorry
