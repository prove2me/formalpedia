-- Prove2me | Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_finite_irreducible
-- name    : BalanceSpecification.hasVariableSpecification_of_finite_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:34.762509+00:00
-- url     : https://prove2.me/theorems/b0eae622-6a44-4c8d-9ad9-810f79537f4b
-- title:
--   Balance Specification: has Variable Specification of finite irreducible
-- statement:
--   The Balance Specification construction uses the has Variable Specification of finite irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L393-L396
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L393-L396

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

theorem BalanceSpecification.hasVariableSpecification_of_finite_irreducible (hfin : X.carrier.Finite)
    (hX : X.carrier.Nonempty) (hirr : Irreducible X) : HasVariableSpecification X := by sorry
