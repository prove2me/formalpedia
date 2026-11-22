-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_not_node_le_bot
-- name    : DeciSigma1.Semantics.PrefixSet.not_node_le_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:30.669772+00:00
-- url     : https://prove2.me/theorems/1774b8fb-c6d1-49a7-a8f8-9fdf8cde838a
-- title:
--   Prefix Set: not node le bot
-- statement:
--   The Prefix Set construction uses the not node le bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L89-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean#L89-L91

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

theorem DeciSigma1.Semantics.PrefixSet.not_node_le_bot (a : Fin n → PrefixSet n) : ¬ node a ≤ bot := by sorry
