-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_Realizes_fill_update
-- name    : DeletionCode.SelectedWindows.Realizes.fill_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:08:51.106377+00:00
-- url     : https://prove2.me/theorems/81034ddf-6515-4918-a05f-9a1d26740c63
-- title:
--   Realizes: fill update
-- statement:
--   Mark a window filled after its checked write extends that bubble's memory.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L202-L209
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L202-L209

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}

theorem DeletionCode.SelectedWindows.Realizes.fill_update [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hwindow : WindowKnown t (windowStart (D b) w) (3 * (k + 1))) :
    Realizes (s.fill b w) (Function.update mem b t) D k := by sorry
