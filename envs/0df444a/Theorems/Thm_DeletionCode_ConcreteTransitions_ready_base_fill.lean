-- Prove2me | Theorems.Thm_DeletionCode_ConcreteTransitions_ready_base_fill
-- name    : DeletionCode.ConcreteTransitions.ready_base_fill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:57:35.597149+00:00
-- url     : https://prove2.me/theorems/6d2bb4e7-c38c-4bab-a676-13827f259e4d
-- title:
--   Concrete Transitions: ready base fill
-- statement:
--   Readiness supplies the seed that makes the executable base fill succeed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L34-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L34-L54

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

theorem DeletionCode.ConcreteTransitions.ready_base_fill [DecidableEq B]
    (s : State B) (mem : B → Memory) (D : B → ℕ) (p : B → Letters)
    (x : Letters) (n k : ℕ) (b : B) (w : Slot)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun a => 3 * (k + 1) + D a))
    (hx : KUnique x n k) (hD : D b < 3 * (k + 1)) (hready : s.Ready b w)
    (hocc : ∃ a, a + 3 * (k + 1) ≤ n ∧
      Agree x a (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ r t, fillFromBase x n k (3 * (k + 1)) (mem b)
        (3 * (k + 1) + D b) (windowStart (D b) w) r = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun a => 3 * (k + 1) + D a) := by sorry
