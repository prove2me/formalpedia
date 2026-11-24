-- Prove2me | Theorems.Thm_BalanceSpecification_isClosed_wordCylinder
-- name    : BalanceSpecification.isClosed_wordCylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:52.837529+00:00
-- url     : https://prove2.me/theorems/0b266db1-71a4-43cb-b472-46916d9962f4
-- title:
--   Balance Specification: is Closed word Cylinder
-- statement:
--   The Balance Specification construction uses the is Closed word Cylinder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L56-L62
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L56-L62

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]

theorem BalanceSpecification.isClosed_wordCylinder (w : Word A) (k : ℤ) : IsClosed (wordCylinder w k) := by sorry
