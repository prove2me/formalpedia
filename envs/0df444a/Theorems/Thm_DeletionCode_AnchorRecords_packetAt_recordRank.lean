-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_packetAt_recordRank
-- name    : DeletionCode.AnchorRecords.packetAt_recordRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:18.441993+00:00
-- url     : https://prove2.me/theorems/02cc03ae-2ae5-4406-9b52-effe3a9f677b
-- title:
--   Anchor Records: packet At record Rank
-- statement:
--   The Anchor Records construction uses the packet At record Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L155-L161
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L155-L161

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.packetAt_recordRank (trace : Trace) (c : EditColumn trace) :
    (encode trace)[recordRank trace c]? =
      some (trace.matchedAnchor c.val.val, payload (column trace c)) := by sorry
