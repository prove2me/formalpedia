-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
-- name    : DeciSigma1.Semantics.Tree.top_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:12.902039+00:00
-- url     : https://prove2.me/theorems/65eae0c3-58cf-4734-98f5-dcb539f9248b
-- title:
--   Tree: top le iff
-- statement:
--   The Tree construction uses the top le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L391-L392
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L391-L392

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
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.Tree.top_le_iff (t : Tree n) : top ≤ t ↔ t = top := by sorry
