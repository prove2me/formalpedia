-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_Realizes_ready_seedKnown
-- name    : DeletionCode.SelectedWindows.Realizes.ready_seedKnown
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:09:10.344363+00:00
-- url     : https://prove2.me/theorems/98e55bed-f2f5-4e19-9fd8-352488434bd9
-- title:
--   Realizes: ready seed Known
-- statement:
--   The Realizes construction uses the ready seed Known property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L131-L137
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L131-L137

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}

theorem DeletionCode.SelectedWindows.Realizes.ready_seedKnown (s : State B) (mem : B → Memory) (D : B → ℕ)
    (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hD : D b < 3 * (k + 1)) (hready : s.Ready b w) :
    SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k := by sorry
