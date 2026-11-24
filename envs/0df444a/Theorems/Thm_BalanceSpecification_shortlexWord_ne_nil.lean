-- Prove2me | Theorems.Thm_BalanceSpecification_shortlexWord_ne_nil
-- name    : BalanceSpecification.shortlexWord_ne_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:37.8736+00:00
-- url     : https://prove2.me/theorems/b06fca16-037f-44b4-aff7-e5f939ff8f04
-- title:
--   Balance Specification: shortlex Word ne nil
-- statement:
--   The Balance Specification construction uses the shortlex Word ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L124-L128
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L124-L128

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

theorem BalanceSpecification.shortlexWord_ne_nil {j : ℕ} (hj : 0 < j) : shortlexWord (A := A) j ≠ [] := by sorry
