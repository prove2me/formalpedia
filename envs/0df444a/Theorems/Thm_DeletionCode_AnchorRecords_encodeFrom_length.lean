-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_encodeFrom_length
-- name    : DeletionCode.AnchorRecords.encodeFrom_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:54:32.722184+00:00
-- url     : https://prove2.me/theorems/1c2f9005-5756-44b0-a4bf-9bcb72bffe88
-- title:
--   Anchor Records: encode From length
-- statement:
--   The Anchor Records construction uses the encode From length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L46-L51
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L46-L51

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.encodeFrom_length (trace : Trace) (m : ℕ) :
    (encodeFrom m trace).length = trace.deletions + trace.insertions := by sorry
