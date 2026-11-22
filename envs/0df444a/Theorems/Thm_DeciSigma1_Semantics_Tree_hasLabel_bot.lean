-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
-- name    : DeciSigma1.Semantics.Tree.hasLabel_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:53.749159+00:00
-- url     : https://prove2.me/theorems/ad0b4405-a8ec-41e2-b35d-127751d7fce5
-- title:
--   Tree: has Label bot
-- statement:
--   The Tree construction uses the has Label bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L247-L251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L247-L251

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

theorem DeciSigma1.Semantics.Tree.hasLabel_bot (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.bot ν s ↔ s = Sym.bot := by sorry
