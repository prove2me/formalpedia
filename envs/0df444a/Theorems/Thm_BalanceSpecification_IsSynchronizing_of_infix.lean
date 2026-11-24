-- Prove2me | Theorems.Thm_BalanceSpecification_IsSynchronizing_of_infix
-- name    : BalanceSpecification.IsSynchronizing.of_infix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:29.867672+00:00
-- url     : https://prove2.me/theorems/7d6eba27-682b-4c22-b704-533b233ccf39
-- title:
--   Is Synchronizing: of infix
-- statement:
--   Every admissible word containing a synchronizing word is synchronizing.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L34-L46
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L34-L46

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}

theorem BalanceSpecification.IsSynchronizing.of_infix (hL : IsFactorial L) {v w : Word A}
    (hv : IsSynchronizing L v) (hw : w ∈ L) (hvw : v <:+: w) :
    IsSynchronizing L w := by sorry
