-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_compatible_of_sound
-- name    : DeletionCode.PartialWords.compatible_of_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:14.511884+00:00
-- url     : https://prove2.me/theorems/29ffae00-ac9b-47f1-8765-4c014b3ac49b
-- title:
--   Partial Words: compatible of sound
-- statement:
--   The Partial Words construction uses the compatible of sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L90-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L90-L99

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.compatible_of_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    Compatible s start bits := by sorry
