-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
-- name    : DeciSigma1.Semantics.Tree.trace_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:46.588211+00:00
-- url     : https://prove2.me/theorems/4453873a-ec81-43b0-8b93-6e6c32db31ae
-- title:
--   Tree: trace bot
-- statement:
--   The Tree construction uses the trace bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L217-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L217-L218

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.trace_bot (ν : List (Fin n)) : trace Tree.bot ν = Tree.bot := by sorry
