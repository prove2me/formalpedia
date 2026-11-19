-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_writeBits_extends
-- name    : DeletionCode.PartialWords.writeBits_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:45.208187+00:00
-- url     : https://prove2.me/theorems/11d1e1f6-2846-4758-8b5d-460f0ad38a4e
-- title:
--   Partial Words: write Bits extends
-- statement:
--   Every successful checked write preserves all previously known bits.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L145-L152
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L145-L152

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.writeBits_extends (s t : Memory) (m start len : ℕ) (bits : Bits len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by sorry
