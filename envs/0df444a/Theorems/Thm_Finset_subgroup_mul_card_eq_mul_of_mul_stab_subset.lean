-- Prove2me | Theorems.Thm_Finset_subgroup_mul_card_eq_mul_of_mul_stab_subset
-- name    : Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:51.99054+00:00
-- url     : https://prove2.me/theorems/89e99978-4585-5ca4-873e-e53f6e7544e2
-- title:
--   Finset: subgroup mul card eq mul of mul stab subset
-- statement:
--   The Finset construction uses the subgroup mul card eq mul of mul stab subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L368-L376
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L368-L376

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
open Finset
variable {ι α : Type*}
local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s
variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #(t +ₛ s) = #t := by sorry
