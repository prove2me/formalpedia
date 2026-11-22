-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeLe_refl
-- name    : DeciSigma1.Semantics.treeLe_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:13.524383+00:00
-- url     : https://prove2.me/theorems/ee0f6f7f-bc79-4a05-a22f-e0a14065aed3
-- title:
--   Semantics: tree Le refl
-- statement:
--   The Semantics construction uses the tree Le refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L383-L384
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L383-L384

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

theorem DeciSigma1.Semantics.treeLe_refl (c : Fin n → Bool) (t : Tree n) : Le c t t := by sorry
