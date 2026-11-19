-- Prove2me | Theorems.Thm_DeletionCode_ConcreteInitialization_initialization_exists
-- name    : DeletionCode.ConcreteInitialization.initialization_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:47.220756+00:00
-- url     : https://prove2.me/theorems/12cfceeb-076f-41f0-806b-ce2007a3b503
-- title:
--   Concrete Initialization: initialization exists
-- statement:
--   Root loading constructs the actual invariant for the abstract initial state.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L97-L131
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L97-L131

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteInitialization.initialization_exists [Fintype B] [DecidableEq B] (M : Model B x n k) :
    ∃ records mem, records.length = rootCount M ∧
      loadRoots x n k M.header (fun _ => empty) records = some mem ∧
      M.Invariant (Recovery.initial M.schedule) mem := by sorry
