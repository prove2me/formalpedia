-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_complete_le_node
-- name    : DeciSigma1.Semantics.PrefixSet.complete_le_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:05.732161+00:00
-- url     : https://prove2.me/theorems/57e50cd5-f1f4-4508-8be1-5e2ed0729af1
-- title:
--   Prefix Set: complete le node
-- statement:
--   The complete tree of depth `d` lies below `f` applied to copies of itself, which is the
--   complete tree of depth `d + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L123-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L123-L127

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
open DeciSigma1.Semantics.PrefixSet

theorem DeciSigma1.Semantics.PrefixSet.complete_le_node (d : ℕ) : complete d ≤ node fun _ => (complete d : PrefixSet n) := by sorry
