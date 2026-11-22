-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_node
-- name    : DeciSigma1.Semantics.normalize_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:06.616125+00:00
-- url     : https://prove2.me/theorems/f1b0be71-fa8c-4447-80bb-1732c93f1b15
-- title:
--   Semantics: normalize node
-- statement:
--   The Semantics construction uses the normalize node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L124-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L124-L130

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_node (c : Fin n → Bool) (p : Bool) (a : Fin n → Tree n) :
    Tree.normalize c p (Tree.node a) =
        Tree.node (fun i => Tree.normalize c (Bool.xor p (c i)) (a i)) := by sorry
