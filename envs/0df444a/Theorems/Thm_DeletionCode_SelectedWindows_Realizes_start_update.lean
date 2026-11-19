-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_Realizes_start_update
-- name    : DeletionCode.SelectedWindows.Realizes.start_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:09:29.244415+00:00
-- url     : https://prove2.me/theorems/167317dd-680a-43ff-ba8f-d5abb23a0d1f
-- title:
--   Realizes: start update
-- statement:
--   Start a chosen slot after extending just that bubble's memory.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L192-L199
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L192-L199

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}

theorem DeletionCode.SelectedWindows.Realizes.start_update [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hseed : SeedKnown t (windowStart (D b) w) (3 * (k + 1)) k) :
    Realizes (s.start b w) (Function.update mem b t) D k := by sorry
