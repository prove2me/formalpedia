-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_negativeLength_pos
-- name    : DeletionCode.RecordBounds.negativeLength_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:16:15.634654+00:00
-- url     : https://prove2.me/theorems/5bb03303-4be5-4036-96cb-3356d696b143
-- title:
--   Record Bounds: negative Length pos
-- statement:
--   The Record Bounds construction uses the negative Length pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L17-L21
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L17-L21

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec

theorem DeletionCode.RecordBounds.negativeLength_pos (k : ℕ) (h : Header)
    (hlo : 1 ≤ h.rho) (hhi : h.rho ≤ k + 1) : 0 < negativeLength k h := by sorry
