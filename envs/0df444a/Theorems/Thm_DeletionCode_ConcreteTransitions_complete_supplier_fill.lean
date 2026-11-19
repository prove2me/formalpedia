-- Prove2me | Theorems.Thm_DeletionCode_ConcreteTransitions_complete_supplier_fill
-- name    : DeletionCode.ConcreteTransitions.complete_supplier_fill
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:57:39.923745+00:00
-- url     : https://prove2.me/theorems/3aff4375-0729-4bdf-bdc2-9720b0d9c10a
-- title:
--   Concrete Transitions: complete supplier fill
-- statement:
--   A completed negative supplier makes any in-bounds source window readable.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L57-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L57-L79

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

theorem DeletionCode.ConcreteTransitions.complete_supplier_fill [DecidableEq B]
    (s : State B) (mem : B → Memory) (D : B → ℕ) (p : B → Letters)
    (k : ℕ) (a b : B) (w : Slot) (sourceStart : ℕ)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun c => 3 * (k + 1) + D c))
    (hD : D a ≤ 3 * (k + 1)) (hcomplete : s.Complete a)
    (hsource : sourceStart ≤ D a)
    (hagree : Agree (p a) sourceStart (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ t, copyFromMemory (mem a) (3 * (k + 1) + D a) sourceStart (3 * (k + 1))
        (mem b) (3 * (k + 1) + D b) (windowStart (D b) w) = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun c => 3 * (k + 1) + D c) := by sorry
