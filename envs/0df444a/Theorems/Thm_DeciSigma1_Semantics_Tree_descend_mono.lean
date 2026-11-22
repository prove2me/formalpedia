-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_descend_mono
-- name    : DeciSigma1.Semantics.Tree.descend_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:49.954571+00:00
-- url     : https://prove2.me/theorems/11bd6311-53aa-4237-a21a-992a79507e87
-- title:
--   Tree: descend mono
-- statement:
--   The Tree construction uses the descend mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L226-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L226-L232

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

theorem DeciSigma1.Semantics.Tree.descend_mono {t u : Tree n} (h : t ≤ u) (i : Fin n) :
    descend t i ≤ descend u i := by sorry
