-- Prove2me | Theorems.Thm_DeletionCode_ConcreteTransitions_startNegative_transition
-- name    : DeletionCode.ConcreteTransitions.startNegative_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:03.759024+00:00
-- url     : https://prove2.me/theorems/f7c18eca-0218-4ede-846e-5e9bfdac0e5f
-- title:
--   Concrete Transitions: start Negative transition
-- statement:
--   A correct negative-path seed produces an actual valid start slot.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L82-L100
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean#L82-L100

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

theorem DeletionCode.ConcreteTransitions.startNegative_transition [DecidableEq B]
    (s : State B) (mem : B → Memory) (headers : B → Header) (long : B → Letters)
    (k : ℕ) (b : B) (offset : ℕ) (bits : Bits k)
    (hreal : Realizes s mem (fun a => negativeExtra k (headers a)) k)
    (hs : BankSound mem (fun a => negativePath k (headers a) (long a))
      (fun a => negativeLength k (headers a)))
    (hrho0 : 1 ≤ (headers b).rho) (hrho1 : (headers b).rho ≤ k + 1)
    (hbound : offset + k ≤ negativeLength k (headers b))
    (hseed : PartialWords.Matches bits (negativePath k (headers b) (long b)) offset) :
    ∃ w t, startNegative k (headers b) offset bits (mem b) = some t ∧
      Realizes (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath k (headers a) (long a)) (fun a => negativeLength k (headers a)) := by sorry
