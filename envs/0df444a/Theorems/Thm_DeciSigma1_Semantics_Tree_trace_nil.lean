-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
-- name    : DeciSigma1.Semantics.Tree.trace_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:40.20134+00:00
-- url     : https://prove2.me/theorems/7687e2d1-c9bc-45a6-9a56-078e730190cf
-- title:
--   Tree: trace nil
-- statement:
--   The Tree construction uses the trace nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L214-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L214-L214

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

theorem DeciSigma1.Semantics.Tree.trace_nil (t : Tree n) : trace t [] = t := by sorry

attribute [defeq] DeciSigma1.Semantics.Tree.trace_nil
