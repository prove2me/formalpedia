-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_readBits_sound
-- name    : DeletionCode.PartialWords.readBits_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:03.303373+00:00
-- url     : https://prove2.me/theorems/41a497b1-7bce-471b-804c-82e1005ff63c
-- title:
--   Partial Words: read Bits sound
-- statement:
--   The Partial Words construction uses the read Bits sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L82-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L82-L88

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.readBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hread : readBits s start len = some bits) :
    Matches bits p start := by sorry
