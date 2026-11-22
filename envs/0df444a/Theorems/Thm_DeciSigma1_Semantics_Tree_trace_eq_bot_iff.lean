-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_bot_iff
-- name    : DeciSigma1.Semantics.Tree.trace_eq_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:35.381804+00:00
-- url     : https://prove2.me/theorems/f03eea1f-8818-47c2-ac96-a3b280ef2455
-- title:
--   Tree: trace eq bot iff
-- statement:
--   The Tree construction uses the trace eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L274-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L274-L282

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

theorem DeciSigma1.Semantics.Tree.trace_eq_bot_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.bot ↔ HasLabel t ν Sym.bot := by sorry
