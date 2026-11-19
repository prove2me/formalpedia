-- Prove2me | Theorems.Thm_DeletionCode_ConcreteRecovery_decode_exists
-- name    : DeletionCode.ConcreteRecovery.decode_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:14:57.198735+00:00
-- url     : https://prove2.me/theorems/ee8e5faf-f840-49ba-ab28-e0fa82e634e3
-- title:
--   Concrete Recovery: decode exists
-- statement:
--   Actual root positions and at most 4|B| instructions decode the modeled words.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L71-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L71-L82

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteRecovery.decode_exists (M : Model B x n k) (hx : KUnique x n k) :
    ∃ roots instructions,
      roots.length = ConcreteInitialization.rootCount M ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k M.header roots instructions =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by sorry
