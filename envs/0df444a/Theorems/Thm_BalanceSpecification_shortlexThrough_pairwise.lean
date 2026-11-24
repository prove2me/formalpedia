-- Prove2me | Theorems.Thm_BalanceSpecification_shortlexThrough_pairwise
-- name    : BalanceSpecification.shortlexThrough_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:33.667797+00:00
-- url     : https://prove2.me/theorems/340d9137-8806-4376-ae6f-b0a1c3f000cf
-- title:
--   Balance Specification: shortlex Through pairwise
-- statement:
--   The Balance Specification construction uses the shortlex Through pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L58-L70
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L58-L70

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

theorem BalanceSpecification.shortlexThrough_pairwise (n : ℕ) :
    (shortlexThrough (A := A) n).Pairwise (List.Shortlex (· < ·)) := by sorry
