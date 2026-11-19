-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_writeBits_correct
-- name    : DeletionCode.PartialWords.writeBits_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:01.730111+00:00
-- url     : https://prove2.me/theorems/b62a7b8f-ebf5-4b1e-8b9d-c2a6fe34f8cf
-- title:
--   Partial Words: write Bits correct
-- statement:
--   Correct data written to correct memory remains correct and can be read back.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L155-L164
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L155-L164

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.writeBits_correct (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by sorry
