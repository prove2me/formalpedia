-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_putBits_at
-- name    : DeletionCode.PartialWords.putBits_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:14.965629+00:00
-- url     : https://prove2.me/theorems/6932f409-fc57-4886-8069-6a0a36d7464c
-- title:
--   Partial Words: put Bits at
-- statement:
--   The Partial Words construction uses the put Bits at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L101-L103
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L101-L103

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.putBits_at (s : Memory) (start len : ℕ) (bits : Bits len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by sorry
