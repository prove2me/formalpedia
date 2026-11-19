-- Prove2me | Theorems.Thm_DeletionCode_ConcreteInitialization_root_records_exist
-- name    : DeletionCode.ConcreteInitialization.root_records_exist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:21.068552+00:00
-- url     : https://prove2.me/theorems/19cfede3-ace0-44a5-949a-4b280257b9f1
-- title:
--   Concrete Initialization: root records exist
-- statement:
--   Exactly one actual x-position is recorded for every marked root.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L68-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L68-L94

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteInitialization.root_records_exist [Fintype B] (M : Model B x n k) :
    ∃ records : List (B × ℕ), records.length = rootCount M ∧ ValidRoots M records ∧
      (∀ b, M.schedule.root b → ∃ a, (b, a) ∈ records) := by sorry
