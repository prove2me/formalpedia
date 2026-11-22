-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
-- name    : DeciSigma1.Semantics.Tree.trace_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:47.752103+00:00
-- url     : https://prove2.me/theorems/c4dbfb8c-25bd-4ec2-b8e4-6dc4f23c6466
-- title:
--   Tree: trace cons
-- statement:
--   The Tree construction uses the trace cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L215-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L215-L216

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

theorem DeciSigma1.Semantics.Tree.trace_cons (t : Tree n) (i : Fin n) (ν : List (Fin n)) :
    trace t (i :: ν) = trace (descend t i) ν := by sorry

attribute [defeq] DeciSigma1.Semantics.Tree.trace_cons
