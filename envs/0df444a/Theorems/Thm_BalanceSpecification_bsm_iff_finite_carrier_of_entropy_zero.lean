-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_finite_carrier_of_entropy_zero
-- name    : BalanceSpecification.bsm_iff_finite_carrier_of_entropy_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:52.197654+00:00
-- url     : https://prove2.me/theorems/edab4407-84c1-47c4-8a7c-9351eb555bcf
-- title:
--   Balance Specification: bsm iff finite carrier of entropy zero
-- statement:
--   On a nonempty zero-entropy shift, BSM is equivalent to finiteness of the shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L107-L122
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L107-L122

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.bsm_iff_finite_carrier_of_entropy_zero (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) :
    BoundedlySupermultiplicative (language X) ↔ X.carrier.Finite := by sorry
