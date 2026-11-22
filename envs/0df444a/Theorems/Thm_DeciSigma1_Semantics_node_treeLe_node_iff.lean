-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
-- name    : DeciSigma1.Semantics.node_treeLe_node_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:07.829802+00:00
-- url     : https://prove2.me/theorems/7429d3bb-f36a-4410-a02f-c40268082a42
-- title:
--   Semantics: node tree Le node iff
-- statement:
--   The Semantics construction uses the node tree Le node iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L404-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L404-L407

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.node_treeLe_node_iff (c : Fin n → Bool) (a b : Fin n → Tree n) :
    Le c (node a) (node b) ↔ ∀ i, if c i then Le c (b i) (a i) else Le c (a i) (b i) := by sorry
