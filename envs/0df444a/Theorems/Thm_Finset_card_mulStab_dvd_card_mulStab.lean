-- Prove2me | Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab
-- name    : Finset.card_mulStab_dvd_card_mulStab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:47.251079+00:00
-- url     : https://prove2.me/theorems/8891e85c-6173-5cd9-9447-c77e244879a6
-- title:
--   Finset: card mul Stab dvd card mul Stab
-- statement:
--   The Finset construction uses the card mul Stab dvd card mul Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L281-L296
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L281-L296

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

theorem Finset.card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by sorry
