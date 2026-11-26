-- Prove2me | Theorems.Thm_Finset_mulStab_quotient_commute_subgroup
-- name    : Finset.mulStab_quotient_commute_subgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:54.078108+00:00
-- url     : https://prove2.me/theorems/9d268c00-b409-535b-a8ff-cc8e74f3e11a
-- title:
--   Finset: mul Stab quotient commute subgroup
-- statement:
--   The Finset construction uses the mul Stab quotient commute subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L379-L421
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L379-L421

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

theorem Finset.mulStab_quotient_commute_subgroup (s : Subgroup α) [DecidablePred (· ∈ s)] (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) : (t.mulStab +ₛ s) = (t +ₛ s).mulStab := by sorry
