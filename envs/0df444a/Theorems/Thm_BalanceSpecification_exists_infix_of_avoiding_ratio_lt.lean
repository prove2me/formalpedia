-- Prove2me | Theorems.Thm_BalanceSpecification_exists_infix_of_avoiding_ratio_lt
-- name    : BalanceSpecification.exists_infix_of_avoiding_ratio_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:43.34555+00:00
-- url     : https://prove2.me/theorems/7092978f-f1d5-4722-afa1-0d5b71b8b620
-- title:
--   Balance Specification: exists infix of avoiding ratio lt
-- statement:
--   A family occupying a larger fraction than all avoiding words contains `v`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L44-L57
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L44-L57

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

theorem BalanceSpecification.exists_infix_of_avoiding_ratio_lt {v : Word A} {N : ℕ}
    {s : Finset (Word A)} (hs : s ⊆ wordFinset L N)
    (hsmall : (wordCount (avoidingLanguage L v) N : ℝ) / wordCount L N <
      (s.card : ℝ) / wordCount L N) :
    ∃ w ∈ s, v <:+: w := by sorry
