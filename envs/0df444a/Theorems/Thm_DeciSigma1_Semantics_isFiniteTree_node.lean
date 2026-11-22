-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isFiniteTree_node
-- name    : DeciSigma1.Semantics.isFiniteTree_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:13.703425+00:00
-- url     : https://prove2.me/theorems/067650ce-bb1d-432b-9ee6-41d3945dc121
-- title:
--   Semantics: is Finite Tree node
-- statement:
--   A constructor applied to finite trees gives a finite tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L163-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L163-L170

module
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.isFiniteTree_node (a : Fin n → PrefixSet n) (ha : ∀ i, IsFiniteTree (a i)) :
    IsFiniteTree (PrefixSet.node a) := by sorry
