-- Prove2me | Theorems.Thm_DeletionCode_ConcreteInitialization_loadRoots_correct
-- name    : DeletionCode.ConcreteInitialization.loadRoots_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:21.509768+00:00
-- url     : https://prove2.me/theorems/b662a3f8-872b-4c57-b8d3-baa93c9c79d7
-- title:
--   Concrete Initialization: load Roots correct
-- statement:
--   Loading valid root records succeeds and preserves every previously stored bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L19-L61
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean#L19-L61

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteInitialization.loadRoots_correct [DecidableEq B] (M : Model B x n k)
    (records : List (B × ℕ)) (mem : Bank B) (hs : M.Sound mem)
    (hvalid : ValidRoots M records) :
    ∃ result, loadRoots x n k M.header mem records = some result ∧ M.Sound result ∧
      (∀ b, Extends (mem b) (result b)) ∧
      (∀ b a, (b, a) ∈ records →
        WindowKnown (result b) 0 (negativeLength k (M.header b))) := by sorry
