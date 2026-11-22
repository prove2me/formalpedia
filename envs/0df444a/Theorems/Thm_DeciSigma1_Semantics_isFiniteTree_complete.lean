-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isFiniteTree_complete
-- name    : DeciSigma1.Semantics.isFiniteTree_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:14.752211+00:00
-- url     : https://prove2.me/theorems/6a47c165-c834-42cf-8978-a711e6d67384
-- title:
--   Semantics: is Finite Tree complete
-- statement:
--   The complete tree of depth `d` is finite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L173-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L173-L174

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

theorem DeciSigma1.Semantics.isFiniteTree_complete (d : ℕ) : IsFiniteTree (PrefixSet.complete d : PrefixSet n) := by sorry
