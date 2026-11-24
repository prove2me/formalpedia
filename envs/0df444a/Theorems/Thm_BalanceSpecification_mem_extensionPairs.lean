-- Prove2me | Theorems.Thm_BalanceSpecification_mem_extensionPairs
-- name    : BalanceSpecification.mem_extensionPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:58.914082+00:00
-- url     : https://prove2.me/theorems/c57b3c1e-e460-4929-8800-930f9a63e275
-- title:
--   Balance Specification: mem extension Pairs
-- statement:
--   The Balance Specification construction uses the mem extension Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L25-L29
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L25-L29

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.mem_extensionPairs {u p s : Word A} {a b : ℕ} :
    (⟨p, s⟩ : (_ : Word A) × Word A) ∈ extensionPairs L u a b ↔
      p ∈ predecessorFinset L u a ∧ s ∈ followerFinset L (p ++ u) b := by sorry
