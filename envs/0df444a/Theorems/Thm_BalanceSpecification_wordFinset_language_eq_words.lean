-- Prove2me | Theorems.Thm_BalanceSpecification_wordFinset_language_eq_words
-- name    : BalanceSpecification.wordFinset_language_eq_words
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:20.654202+00:00
-- url     : https://prove2.me/theorems/b9d28eff-4e9d-4072-a982-24da97e769bc
-- title:
--   Balance Specification: word Finset language eq words
-- statement:
--   Set and finite-set presentations of `𝓑_n(X)` agree exactly.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L97-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L97-L100

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]

theorem BalanceSpecification.wordFinset_language_eq_words [TopologicalSpace A] (X : ShiftSpace A) (n : ℕ) :
    (wordFinset (language X) n : Set (Word A)) = words X n := by sorry
