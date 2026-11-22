-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_node
-- name    : DeciSigma1.Semantics.dual_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:21.455634+00:00
-- url     : https://prove2.me/theorems/fb0d5764-500d-4124-bdba-e67de0581c87
-- title:
--   Semantics: dual node
-- statement:
--   The Semantics construction uses the dual node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L146-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L146-L147

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_node (a : Fin n → Tree n) :
    Tree.dual (Tree.node a) = Tree.node (fun i => Tree.dual (a i)) := by sorry
