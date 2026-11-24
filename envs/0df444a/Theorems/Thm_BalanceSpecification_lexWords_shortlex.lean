-- Prove2me | Theorems.Thm_BalanceSpecification_lexWords_shortlex
-- name    : BalanceSpecification.lexWords_shortlex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:24.326931+00:00
-- url     : https://prove2.me/theorems/1a3026e8-a3f4-41b1-9d3b-2e12eacae171
-- title:
--   Balance Specification: lex Words shortlex
-- statement:
--   The Balance Specification construction uses the lex Words shortlex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L52-L56
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L52-L56

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

theorem BalanceSpecification.lexWords_shortlex (n : ℕ) :
    (lexWords (A := A) n).Pairwise (List.Shortlex (· < ·)) := by sorry
