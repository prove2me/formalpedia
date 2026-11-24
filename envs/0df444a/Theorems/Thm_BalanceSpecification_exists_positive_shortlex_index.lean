-- Prove2me | Theorems.Thm_BalanceSpecification_exists_positive_shortlex_index
-- name    : BalanceSpecification.exists_positive_shortlex_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:43:40.837453+00:00
-- url     : https://prove2.me/theorems/e3197f12-f53f-4cf2-9a71-9a9740208b96
-- title:
--   Balance Specification: exists positive shortlex index
-- statement:
--   The Balance Specification construction uses the exists positive shortlex index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L130-L137
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L130-L137

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

theorem BalanceSpecification.exists_positive_shortlex_index {w : Word A} (hw : w ≠ []) :
    ∃ j : ℕ, 1 ≤ j ∧ shortlexWord (A := A) j = w := by sorry
