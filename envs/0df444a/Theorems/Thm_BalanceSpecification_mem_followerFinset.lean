-- Prove2me | Theorems.Thm_BalanceSpecification_mem_followerFinset
-- name    : BalanceSpecification.mem_followerFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:41.605816+00:00
-- url     : https://prove2.me/theorems/a6a9e0f5-05d0-4b28-b0d8-35a596ab7d5a
-- title:
--   Balance Specification: mem follower Finset
-- statement:
--   The Balance Specification construction uses the mem follower Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L54-L57
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L54-L57

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

theorem BalanceSpecification.mem_followerFinset {L : Set (Word A)} {u w : Word A} {n : ℕ} :
    w ∈ followerFinset L u n ↔ w ∈ L ∧ w.length = n ∧ u ++ w ∈ L := by sorry
