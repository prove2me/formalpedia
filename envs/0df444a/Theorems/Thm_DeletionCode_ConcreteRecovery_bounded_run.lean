-- Prove2me | Theorems.Thm_DeletionCode_ConcreteRecovery_bounded_run
-- name    : DeletionCode.ConcreteRecovery.bounded_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:54.648269+00:00
-- url     : https://prove2.me/theorems/8926282a-6733-4889-bc8c-d2af1c384157
-- title:
--   Concrete Recovery: bounded run
-- statement:
--   The Concrete Recovery construction uses the bounded run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L16-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean#L16-L50

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteRecovery.bounded_run (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions mem' q,
      run x n k M.header mem instructions = some mem' ∧
      M.Invariant q mem' ∧ (∀ b, q.Complete b) ∧
      instructions.length + s.score ≤ 4 * Fintype.card B := by sorry
