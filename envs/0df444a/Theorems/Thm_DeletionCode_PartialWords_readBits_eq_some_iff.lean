-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_readBits_eq_some_iff
-- name    : DeletionCode.PartialWords.readBits_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:11.046319+00:00
-- url     : https://prove2.me/theorems/5a46c1c3-89dd-4473-b32d-856d0b794180
-- title:
--   Partial Words: read Bits eq some iff
-- statement:
--   The Partial Words construction uses the read Bits eq some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L57-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L57-L80

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.readBits_eq_some_iff (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by sorry
