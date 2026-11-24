-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_eq_zero_of_le
-- name    : BalanceSpecification.wordCount_eq_zero_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:51.741746+00:00
-- url     : https://prove2.me/theorems/c05e9690-7e3f-49cf-8679-dff0e7f30509
-- title:
--   Balance Specification: word Count eq zero of le
-- statement:
--   In a factorial language, once a length has no words, all larger lengths
--   also have no words. This includes length zero.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L100-L112
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L100-L112

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.wordCount_eq_zero_of_le (hL : IsFactorial L) {m n : ℕ}
    (hm : wordCount L m = 0) (hmn : m ≤ n) : wordCount L n = 0 := by sorry
