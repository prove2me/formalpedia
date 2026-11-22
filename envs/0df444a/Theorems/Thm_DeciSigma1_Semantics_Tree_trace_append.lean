-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_append
-- name    : DeciSigma1.Semantics.Tree.trace_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:36.967231+00:00
-- url     : https://prove2.me/theorems/4e2e8af6-6f69-423c-8a59-83fc82ed4426
-- title:
--   Tree: trace append
-- statement:
--   The Tree construction uses the trace append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L222-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L222-L224

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

theorem DeciSigma1.Semantics.Tree.trace_append (t : Tree n) (ν μ : List (Fin n)) :
    trace t (ν ++ μ) = trace (trace t ν) μ := by sorry
