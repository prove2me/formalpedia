-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegularTree_univ
-- name    : DeciSigma1.Semantics.isRegularTree_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:32.983277+00:00
-- url     : https://prove2.me/theorems/20323bd0-a257-46a9-b870-f68dda232a1b
-- title:
--   Semantics: is Regular Tree univ
-- statement:
--   The tree `PrefixSet.univ` is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L151-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L151-L154

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

theorem DeciSigma1.Semantics.isRegularTree_univ : IsRegularTree (PrefixSet.univ : PrefixSet n) := by sorry
