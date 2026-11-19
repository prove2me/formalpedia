-- Prove2me | Theorems.Thm_DeletionCode_PartialWords_empty_sound
-- name    : DeletionCode.PartialWords.empty_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:40.851495+00:00
-- url     : https://prove2.me/theorems/35480a93-1f06-4c25-ade7-51bdca41fa67
-- title:
--   Partial Words: empty sound
-- statement:
--   The Partial Words construction uses the empty sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L53-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean#L53-L55

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows

theorem DeletionCode.PartialWords.empty_sound (p : Letters) (m : ℕ) : Sound empty p m := by sorry
