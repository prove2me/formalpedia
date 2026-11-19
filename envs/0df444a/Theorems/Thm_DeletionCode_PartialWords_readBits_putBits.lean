-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_readBits_putBits
-- name    : DeletionCode.PartialWords.readBits_putBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:29.883343+00:00
-- url     : https://prove2.me/theorems/bee63561-83c5-4ee3-a3ac-bee4b29d5774
-- title:
--   Partial Words: read Bits put Bits
-- statement:
--   The Partial Words construction uses the read Bits put Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L133-L136
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L133-L136

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.readBits_putBits (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits (putBits s start bits) start len = some bits := by sorry
