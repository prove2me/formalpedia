-- Prove2me | Theorems.Thm_Finset_inter_mul_sub_card_le
-- name    : Finset.inter_mul_sub_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:15.537486+00:00
-- url     : https://prove2.me/theorems/bfd87fca-bee4-4d35-84fa-a55f102767e5
-- title:
--   Finset: inter mul sub card le
-- statement:
--   The Finset construction uses the inter mul sub card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L223-L267
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L223-L267

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset

theorem Finset.inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by sorry
