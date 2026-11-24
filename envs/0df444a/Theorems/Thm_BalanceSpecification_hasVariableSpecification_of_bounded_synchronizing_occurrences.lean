-- Prove2me | Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_bounded_synchronizing_occurrences
-- name    : BalanceSpecification.hasVariableSpecification_of_bounded_synchronizing_occurrences
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:37.32063+00:00
-- url     : https://prove2.me/theorems/35216c34-8b67-4447-8500-2335b8c2e50c
-- title:
--   Balance Specification: has Variable Specification of bounded synchronizing occurrences
-- statement:
--   Uniform bounded follower and predecessor occurrences of one synchronizing
--   word imply variable specification, with a bridge bound of `2 * N`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L74-L85
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L74-L85

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}

theorem BalanceSpecification.hasVariableSpecification_of_bounded_synchronizing_occurrences
    [TopologicalSpace A] {X : ShiftSpace A} {v : Word A}
    (hv : IsSynchronizing (language X) v) {N : ℕ}
    (hF : ∀ u ∈ language X, ∃ s : Word A,
      s.length ≤ N ∧ u ++ s ∈ language X ∧ v <:+: s)
    (hP : ∀ w ∈ language X, ∃ p : Word A,
      p.length ≤ N ∧ p ++ w ∈ language X ∧ v <:+: p) :
    HasVariableSpecification X := by sorry
