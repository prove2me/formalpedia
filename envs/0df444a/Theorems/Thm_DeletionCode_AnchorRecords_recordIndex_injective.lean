-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_recordIndex_injective
-- name    : DeletionCode.AnchorRecords.recordIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:16.205853+00:00
-- url     : https://prove2.me/theorems/b560cdb1-d4c0-47a4-aee1-8d98ea2783b0
-- title:
--   Anchor Records: record Index injective
-- statement:
--   The Anchor Records construction uses the record Index injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L189-L199
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L189-L199

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.recordIndex_injective (trace : Trace) : Function.Injective (recordIndex trace) := by sorry
