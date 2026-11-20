-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_encodeFrom_anchor_bounds
-- name    : DeletionCode.AnchorRecords.encodeFrom_anchor_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:23.292776+00:00
-- url     : https://prove2.me/theorems/ff68fc14-6fe8-481f-9b3d-59834356fbe4
-- title:
--   Anchor Records: encode From anchor bounds
-- statement:
--   The Anchor Records construction uses the encode From anchor bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L56-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L56-L76

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.encodeFrom_anchor_bounds (trace : Trace) (m : ℕ) (p : Packet)
    (hp : p ∈ encodeFrom m trace) :
    m ≤ p.1 ∧ p.1 ≤ m + trace.matchedCount := by sorry
