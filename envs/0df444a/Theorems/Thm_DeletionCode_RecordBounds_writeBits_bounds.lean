-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_writeBits_bounds
-- name    : DeletionCode.RecordBounds.writeBits_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:16:27.640403+00:00
-- url     : https://prove2.me/theorems/65c97e89-0825-4004-8a17-eadbf7138fdf
-- title:
--   Record Bounds: write Bits bounds
-- statement:
--   The Record Bounds construction uses the write Bits bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L23-L29
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L23-L29

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec

theorem DeletionCode.RecordBounds.writeBits_bounds (s t : Memory) (m start len : ℕ) (bits : PartialWords.Bits len)
    (h : writeBits s m start bits = some t) : start + len ≤ m := by sorry
