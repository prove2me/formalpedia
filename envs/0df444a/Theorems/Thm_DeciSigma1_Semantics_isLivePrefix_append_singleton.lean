-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isLivePrefix_append_singleton
-- name    : DeciSigma1.Semantics.isLivePrefix_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:08.67231+00:00
-- url     : https://prove2.me/theorems/fc6127dc-b9fd-4751-bdca-7249ed59d66b
-- title:
--   Semantics: is Live Prefix append singleton
-- statement:
--   The Semantics construction uses the is Live Prefix append singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L82-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L82-L104

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.isLivePrefix_append_singleton (labels : List (Fin n) → Sym)
    (π : List (Fin n)) (i : Fin n) :
    IsLivePrefix labels (π ++ [i]) ↔ IsLivePrefix labels π ∧ labels π = .f := by sorry
