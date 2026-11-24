-- Prove2me | Theorems.Thm_BalanceSpecification_strictMono_int_cofinal
-- name    : BalanceSpecification.strictMono_int_cofinal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:15.499528+00:00
-- url     : https://prove2.me/theorems/ad29622b-5244-4e01-a8f1-b63207cbba9d
-- title:
--   Balance Specification: strict Mono int cofinal
-- statement:
--   A strictly increasing integer sequence has cuts on both sides of any
--   specified integer coordinate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L19-L47
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L19-L47

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.strictMono_int_cofinal {p : ℤ → ℤ} (hp : StrictMono p) (k : ℤ) :
    (∃ i, p i ≤ k) ∧ (∃ j, k ≤ p j) := by sorry
