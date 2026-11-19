-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_putBits_sound
-- name    : DeletionCode.PartialWords.putBits_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:23.844357+00:00
-- url     : https://prove2.me/theorems/dd1b414a-13ec-448e-8ea5-560d3d99697e
-- title:
--   Partial Words: put Bits sound
-- statement:
--   The Partial Words construction uses the put Bits sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L120-L131
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L120-L131

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.putBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by sorry
