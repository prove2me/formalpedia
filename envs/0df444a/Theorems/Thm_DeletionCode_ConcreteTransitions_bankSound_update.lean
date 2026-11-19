-- Prove2me | Theorems.Thm_DeletionCode_ConcreteTransitions_bankSound_update
-- name    : DeletionCode.ConcreteTransitions.bankSound_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:08:33.651222+00:00
-- url     : https://prove2.me/theorems/df520408-0fab-4ba5-865d-11c31cb7352d
-- title:
--   Concrete Transitions: bank Sound update
-- statement:
--   The Concrete Transitions construction uses the bank Sound update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L23-L31
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L23-L31

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteTransitions
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteTransitions
open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)
variable {B : Type*}

theorem DeletionCode.ConcreteTransitions.bankSound_update [DecidableEq B] (mem : B → Memory) (p : B → Letters)
    (len : B → ℕ) (hs : BankSound mem p len) (b : B) (t : Memory)
    (ht : Sound t (p b) (len b)) : BankSound (Function.update mem b t) p len := by sorry
