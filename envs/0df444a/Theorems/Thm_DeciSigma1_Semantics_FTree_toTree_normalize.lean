-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
-- name    : DeciSigma1.Semantics.FTree.toTree_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:34.883363+00:00
-- url     : https://prove2.me/theorems/e187cd1f-0c09-44e9-a2d1-5508dd92b74b
-- title:
--   FTree: to Tree normalize
-- statement:
--   The FTree construction uses the to Tree normalize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L174-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L174-L179

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.FTree.toTree_normalize (c : Fin n → Bool) (p : Bool) (t : FTree n) :
    (t.normalize c p).toTree = Tree.normalize c p t.toTree := by sorry
