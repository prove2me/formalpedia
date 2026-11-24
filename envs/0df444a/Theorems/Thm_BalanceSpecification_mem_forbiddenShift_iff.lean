-- Prove2me | Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
-- name    : BalanceSpecification.mem_forbiddenShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:09.245348+00:00
-- url     : https://prove2.me/theorems/3db3a368-6aa2-4a0c-9f1a-b38ca0c8e5e5
-- title:
--   Balance Specification: mem forbidden Shift iff
-- statement:
--   The Balance Specification construction uses the mem forbidden Shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L93-L95
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L93-L95

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

theorem BalanceSpecification.mem_forbiddenShift_iff {F : Set (Word A)} {x : Configuration A} :
    x ∈ (forbiddenShift F).carrier ↔ ∀ w ∈ F, ∀ k : ℤ, block x k w.length ≠ w := by sorry
