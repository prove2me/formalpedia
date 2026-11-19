-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_writeBits_success
-- name    : DeletionCode.PartialWords.writeBits_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:37.052668+00:00
-- url     : https://prove2.me/theorems/ce2d6a79-b632-4004-8b44-083620db206c
-- title:
--   Partial Words: write Bits success
-- statement:
--   The Partial Words construction uses the write Bits success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L138-L142
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L138-L142

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.writeBits_success (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by sorry
