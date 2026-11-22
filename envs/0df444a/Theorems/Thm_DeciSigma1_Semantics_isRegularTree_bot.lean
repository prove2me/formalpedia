-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegularTree_bot
-- name    : DeciSigma1.Semantics.isRegularTree_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:05.701055+00:00
-- url     : https://prove2.me/theorems/6670bbdd-6e62-4dac-b5f7-61e75181128f
-- title:
--   Semantics: is Regular Tree bot
-- statement:
--   The tree `⊥` is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L136-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L136-L139

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

theorem DeciSigma1.Semantics.isRegularTree_bot : IsRegularTree (PrefixSet.bot : PrefixSet n) := by sorry
