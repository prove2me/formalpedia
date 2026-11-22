-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
-- name    : DeciSigma1.Semantics.Tree.hasLabel_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:51.949935+00:00
-- url     : https://prove2.me/theorems/5919103b-b560-4cc0-a926-ed1773c60f67
-- title:
--   Tree: has Label top
-- statement:
--   The Tree construction uses the has Label top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L253-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L253-L257

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

theorem DeciSigma1.Semantics.Tree.hasLabel_top (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.top ν s ↔ s = Sym.top := by sorry
