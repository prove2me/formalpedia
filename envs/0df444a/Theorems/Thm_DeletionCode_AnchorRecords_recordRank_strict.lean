-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_recordRank_strict
-- name    : DeletionCode.AnchorRecords.recordRank_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:20.1552+00:00
-- url     : https://prove2.me/theorems/d1666e04-8b1e-43c7-b84a-ae8c0a064c20
-- title:
--   Anchor Records: record Rank strict
-- statement:
--   The Anchor Records construction uses the record Rank strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L170-L187
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L170-L187

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.recordRank_strict (trace : Trace) (c d : EditColumn trace)
    (hcd : c.val.val < d.val.val) : recordRank trace c < recordRank trace d := by sorry
