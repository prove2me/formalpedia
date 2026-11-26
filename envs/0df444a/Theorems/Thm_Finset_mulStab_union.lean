-- Prove2me | Theorems.Thm_Finset_mulStab_union
-- name    : Finset.mulStab_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:11.687827+00:00
-- url     : https://prove2.me/theorems/f2851fef-73a7-47b3-aeeb-f0ad36ec7090
-- title:
--   Finset: mul Stab union
-- statement:
--   The Finset construction uses the mul Stab union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L92-L138
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L92-L138

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

theorem Finset.mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by sorry
