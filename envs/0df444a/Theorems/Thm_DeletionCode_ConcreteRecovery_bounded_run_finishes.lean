-- Prove2me | Theorems.Thm_DeletionCode_ConcreteRecovery_bounded_run_finishes
-- name    : DeletionCode.ConcreteRecovery.bounded_run_finishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:59.14193+00:00
-- url     : https://prove2.me/theorems/354c0086-3aed-4adb-b82a-f2afdfd25af7
-- title:
--   Concrete Recovery: bounded run finishes
-- statement:
--   Bounded concrete execution recovers all finite negative words exactly.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L53-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L53-L65

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteRecovery.bounded_run_finishes (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions,
      instructions.length + s.score ≤ 4 * Fintype.card B ∧
      (run x n k M.header mem instructions).bind (finish k M.header) =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by sorry
