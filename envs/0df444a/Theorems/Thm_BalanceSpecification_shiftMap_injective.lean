-- Prove2me | Theorems.Thm_BalanceSpecification_shiftMap_injective
-- name    : BalanceSpecification.shiftMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:07.749255+00:00
-- url     : https://prove2.me/theorems/3c1b5cd7-54b4-4f1d-91ca-ebea8073b3ff
-- title:
--   Balance Specification: shift Map injective
-- statement:
--   The Balance Specification construction uses the shift Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L130-L137
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L130-L137

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
omit [Fintype A]

theorem BalanceSpecification.shiftMap_injective (X : ShiftSpace A) : Function.Injective (shiftMap X) := by sorry
