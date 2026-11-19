-- Prove2me | Theorems.Thm_DeletionCode_ConcreteTransitions_startPositive_transition
-- name    : DeletionCode.ConcreteTransitions.startPositive_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:03.123717+00:00
-- url     : https://prove2.me/theorems/76791fd1-4ed3-48ec-b13e-4999733944ff
-- title:
--   Concrete Transitions: start Positive transition
-- statement:
--   A correct positive-path seed uses at most one recorded bit and a real start slot.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L103-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L103-L122

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

theorem DeletionCode.ConcreteTransitions.startPositive_transition [DecidableEq B]
    (s : State B) (mem : B → Memory) (headers : B → Header) (long : B → Letters)
    (k : ℕ) (b : B) (offset : ℕ) (bits : Bits k)
    (hreal : Realizes s mem (fun a => negativeExtra k (headers a)) k)
    (hs : BankSound mem (fun a => negativePath k (headers a) (long a))
      (fun a => negativeLength k (headers a)))
    (hrho0 : 1 ≤ (headers b).rho) (hrho1 : (headers b).rho ≤ k + 1)
    (hbit : long b (editOffset k) = (headers b).bit)
    (hbound : offset + k ≤ positiveLength k (headers b))
    (hseed : ∀ i : Fin k, positivePath k (headers b) (long b) (offset + i.val) = bits i) :
    ∃ extra w t, startPositive k (headers b) offset bits extra (mem b) = some t ∧
      Realizes (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath k (headers a) (long a)) (fun a => negativeLength k (headers a)) := by sorry
