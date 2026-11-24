-- Prove2me | Theorems.Thm_BalanceSpecification_length_shortlexWord_le
-- name    : BalanceSpecification.length_shortlexWord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:43.389809+00:00
-- url     : https://prove2.me/theorems/03bab533-611c-4d8e-b804-a1f3507a94c1
-- title:
--   Balance Specification: length shortlex Word le
-- statement:
--   The Balance Specification construction uses the length shortlex Word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L98-L99
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L98-L99

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]

theorem BalanceSpecification.length_shortlexWord_le (j : ℕ) : (shortlexWord (A := A) j).length ≤ j := by sorry
