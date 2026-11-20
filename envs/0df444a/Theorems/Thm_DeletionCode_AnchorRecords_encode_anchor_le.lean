-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_encode_anchor_le
-- name    : DeletionCode.AnchorRecords.encode_anchor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:54:44.496697+00:00
-- url     : https://prove2.me/theorems/d083eeff-3ecd-4bc9-8115-907568ffb9e3
-- title:
--   Anchor Records: encode anchor le
-- statement:
--   The Anchor Records construction uses the encode anchor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L78-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L78-L80

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.encode_anchor_le (trace : Trace) (p : Packet) (hp : p ∈ encode trace) :
    p.1 ≤ trace.matchedCount := by sorry
