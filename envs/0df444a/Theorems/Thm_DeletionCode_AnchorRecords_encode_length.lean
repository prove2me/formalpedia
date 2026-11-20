-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_encode_length
-- name    : DeletionCode.AnchorRecords.encode_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:54:35.151613+00:00
-- url     : https://prove2.me/theorems/08bc569f-9171-4877-8c37-4a5837a50b0b
-- title:
--   Anchor Records: encode length
-- statement:
--   The Anchor Records construction uses the encode length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L53-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L53-L54

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.encode_length (trace : Trace) :
    (encode trace).length = trace.deletions + trace.insertions := by sorry
