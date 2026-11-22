-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegularTree_node
-- name    : DeciSigma1.Semantics.isRegularTree_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:10.777681+00:00
-- url     : https://prove2.me/theorems/aa042697-eb6d-4fa2-821e-ceb071740aaa
-- title:
--   Semantics: is Regular Tree node
-- statement:
--   A constructor applied to regular trees gives a regular tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L142-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L142-L148

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

theorem DeciSigma1.Semantics.isRegularTree_node (a : Fin n → PrefixSet n) (ha : ∀ i, IsRegularTree (a i)) :
    IsRegularTree (PrefixSet.node a) := by sorry
