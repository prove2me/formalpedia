-- Prove2me | Theorems.Thm_BalanceSpecification_topologicallyMixing_of_word_bridges
-- name    : BalanceSpecification.topologicallyMixing_of_word_bridges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:22.124265+00:00
-- url     : https://prove2.me/theorems/73767ff1-d072-4f22-b5fb-d6b889056795
-- title:
--   Balance Specification: topologically Mixing of word bridges
-- statement:
--   Arbitrary sufficiently long language bridges imply genuine open-set mixing.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TopologicalMixing.lean#L58-L95
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TopologicalMixing.lean#L58-L95

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
set_option autoImplicit true
@[expose] public section
public section
open Set TopologicalSpace
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]

theorem BalanceSpecification.topologicallyMixing_of_word_bridges {X : ShiftSpace A}
    (hbridge : ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ K : ℕ, ∀ L : ℕ, K ≤ L →
        ∃ w ∈ language X, w.length = L ∧ u ++ w ++ v ∈ language X) :
    TopologicallyMixing X := by sorry
