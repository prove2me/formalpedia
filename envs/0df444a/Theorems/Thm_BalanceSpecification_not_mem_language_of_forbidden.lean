-- Prove2me | Theorems.Thm_BalanceSpecification_not_mem_language_of_forbidden
-- name    : BalanceSpecification.not_mem_language_of_forbidden
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:11.866884+00:00
-- url     : https://prove2.me/theorems/9a568425-8f39-4800-a44f-6de6e87eac40
-- title:
--   Balance Specification: not mem language of forbidden
-- statement:
--   The Balance Specification construction uses the not mem language of forbidden property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L97-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L97-L100

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

theorem BalanceSpecification.not_mem_language_of_forbidden {F : Set (Word A)} {w : Word A}
    (hw : w ∈ F) : w ∉ language (forbiddenShift F) := by sorry
