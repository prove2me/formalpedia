-- Prove2me | Theorems.Thm_Finset_mulStab_mul_ssubset_mulStab
-- name    : Finset.mulStab_mul_ssubset_mulStab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:14.341449+00:00
-- url     : https://prove2.me/theorems/6c352d2e-03ad-43ae-adfb-fcd51b0389fb
-- title:
--   Finset: mul Stab mul ssubset mul Stab
-- statement:
--   The Finset construction uses the mul Stab mul ssubset mul Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L47-L89
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L47-L89

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

theorem Finset.mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by sorry
