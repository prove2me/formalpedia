-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_get_recordIndex
-- name    : DeletionCode.AnchorRecords.get_recordIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:54:47.865709+00:00
-- url     : https://prove2.me/theorems/d7e571ad-298e-4545-89dd-4488cedb739d
-- title:
--   Anchor Records: get record Index
-- statement:
--   The Anchor Records construction uses the get record Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L163-L168
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L163-L168

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.get_recordIndex (trace : Trace) (c : EditColumn trace) :
    (encode trace).get (recordIndex trace c) =
      (trace.matchedAnchor c.val.val, payload (column trace c)) := by sorry
