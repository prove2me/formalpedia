-- Prove2me | Theorems.Thm_BalanceSpecification_codedShift_synchronizingCode
-- name    : BalanceSpecification.codedShift_synchronizingCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:00.867693+00:00
-- url     : https://prove2.me/theorems/38e1afa4-69f5-423b-bbb7-196635401f39
-- title:
--   Balance Specification: coded Shift synchronizing Code
-- statement:
--   Synchronization supplies an explicit code whose literal closure is `X`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SynchronizedCoded.lean#L70-L85
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SynchronizedCoded.lean#L70-L85

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}

theorem BalanceSpecification.codedShift_synchronizingCode {v : Word A}
    (hirr : Irreducible X) (hv : IsSynchronizing (language X) v) :
    (codedShift (synchronizingCode X v)).carrier = X.carrier := by sorry
