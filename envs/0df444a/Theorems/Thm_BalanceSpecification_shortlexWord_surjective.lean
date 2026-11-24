-- Prove2me | Theorems.Thm_BalanceSpecification_shortlexWord_surjective
-- name    : BalanceSpecification.shortlexWord_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:36.894035+00:00
-- url     : https://prove2.me/theorems/b182c75e-54ae-43de-a588-3d09fbefc9af
-- title:
--   Balance Specification: shortlex Word surjective
-- statement:
--   The Balance Specification construction uses the shortlex Word surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L107-L111
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L107-L111

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

theorem BalanceSpecification.shortlexWord_surjective : Function.Surjective (shortlexWord (A := A)) := by sorry
