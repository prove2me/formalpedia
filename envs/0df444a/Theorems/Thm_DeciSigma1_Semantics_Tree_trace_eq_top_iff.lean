-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_top_iff
-- name    : DeciSigma1.Semantics.Tree.trace_eq_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:37.509607+00:00
-- url     : https://prove2.me/theorems/9a48067e-07d6-4da5-a3ce-dce1647ebd8b
-- title:
--   Tree: trace eq top iff
-- statement:
--   The Tree construction uses the trace eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L284-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L284-L292

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

theorem DeciSigma1.Semantics.Tree.trace_eq_top_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.top ↔ HasLabel t ν Sym.top := by sorry
