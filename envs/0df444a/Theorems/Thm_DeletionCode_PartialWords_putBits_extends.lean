-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_putBits_extends
-- name    : DeletionCode.PartialWords.putBits_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:19.295891+00:00
-- url     : https://prove2.me/theorems/2ac14ce4-fc10-4149-a42f-d499cf6fbb8d
-- title:
--   Partial Words: put Bits extends
-- statement:
--   The Partial Words construction uses the put Bits extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L105-L118
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L105-L118

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.putBits_extends (s : Memory) (start len : ℕ) (bits : Bits len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by sorry
