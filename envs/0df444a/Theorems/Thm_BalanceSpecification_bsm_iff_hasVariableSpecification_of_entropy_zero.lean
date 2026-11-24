-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_hasVariableSpecification_of_entropy_zero
-- name    : BalanceSpecification.bsm_iff_hasVariableSpecification_of_entropy_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:42.359647+00:00
-- url     : https://prove2.me/theorems/80017862-abd6-4ac1-90c6-1a9d547f9c5e
-- title:
--   Balance Specification: bsm iff has Variable Specification of entropy zero
-- statement:
--   For an irreducible zero-entropy shift, BSM and variable specification coincide.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L399-L408
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L399-L408

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

theorem BalanceSpecification.bsm_iff_hasVariableSpecification_of_entropy_zero (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) (hirr : Irreducible X) :
    BoundedlySupermultiplicative (language X) ↔ HasVariableSpecification X := by sorry
