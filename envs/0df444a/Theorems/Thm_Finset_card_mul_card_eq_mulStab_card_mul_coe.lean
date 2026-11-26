-- Prove2me | Theorems.Thm_Finset_card_mul_card_eq_mulStab_card_mul_coe
-- name    : Finset.card_mul_card_eq_mulStab_card_mul_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:49.262656+00:00
-- url     : https://prove2.me/theorems/9ff4109d-7cc1-5311-99cf-4499c8e23879
-- title:
--   Finset: card mul card eq mul Stab card mul coe
-- statement:
--   The Finset construction uses the card mul card eq mul Stab card mul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L315-L327
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L315-L327

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

theorem Finset.card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((s * t) +ₛ stabilizer α (↑(s * t) : Set α)) := by sorry
