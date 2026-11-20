-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_encode_anchor_lt_source
-- name    : DeletionCode.AnchorRecords.encode_anchor_lt_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:19.062073+00:00
-- url     : https://prove2.me/theorems/1c10ff45-dbf3-442b-8c98-7e1e6162096d
-- title:
--   Anchor Records: encode anchor lt source
-- statement:
--   With at least one deletion, every edit anchor is strictly below source length.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L202-L206
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L202-L206

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.encode_anchor_lt_source (trace : Trace) (hd : 1 ≤ trace.deletions)
    (p : Packet) (hp : p ∈ encode trace) : p.1 < trace.source.length := by sorry
