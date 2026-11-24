-- Prove2me | Theorems.Thm_BalanceSpecification_shortlexWord_eq_getElem
-- name    : BalanceSpecification.shortlexWord_eq_getElem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:33.336054+00:00
-- url     : https://prove2.me/theorems/3e165521-b87a-4ac0-8b42-55293d5d56a7
-- title:
--   Balance Specification: shortlex Word eq get Elem
-- statement:
--   The Balance Specification construction uses the shortlex Word eq get Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L101-L105
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L101-L105

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

theorem BalanceSpecification.shortlexWord_eq_getElem {j n : ℕ} (hj : j < (shortlexThrough (A := A) n).length) :
    shortlexWord (A := A) j = (shortlexThrough n)[j] := by sorry
