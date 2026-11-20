-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_startNegative_bounds
-- name    : DeletionCode.RecordBounds.startNegative_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:16:29.781209+00:00
-- url     : https://prove2.me/theorems/83562cfa-d2ac-4208-a2e7-b46f645341b7
-- title:
--   Record Bounds: start Negative bounds
-- statement:
--   The Record Bounds construction uses the start Negative bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L31-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L31-L34

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec

theorem DeletionCode.RecordBounds.startNegative_bounds (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (s t : Memory) (hs : ConcreteStart.startNegative k h offset bits s = some t) :
    offset + k ≤ negativeLength k h := by sorry
