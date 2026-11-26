-- Prove2me | Theorems.Thm_Finset_disjoint_smul_mulStab
-- name    : Finset.disjoint_smul_mulStab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:13.653202+00:00
-- url     : https://prove2.me/theorems/89a724cc-3e75-4707-bb4f-9fd708e45c4c
-- title:
--   Finset: disjoint smul mul Stab
-- statement:
--   The Finset construction uses the disjoint smul mul Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L163-L170
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean#L163-L170

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

theorem Finset.disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by sorry
