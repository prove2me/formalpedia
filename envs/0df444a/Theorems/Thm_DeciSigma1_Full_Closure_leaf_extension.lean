-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leaf_extension
-- name    : DeciSigma1.Full.Closure.leaf_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:22.414819+00:00
-- url     : https://prove2.me/theorems/5c6ae036-2012-401a-8c4a-25010b2b2203
-- title:
--   Closure: leaf extension
-- statement:
--   The Closure construction uses the leaf extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L72-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L72-L77

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Closure.leaf_extension (c : Fin n → Bool) (t : Semantics.Tree n) (s : Bool) :
    ExtensionClosed (leaf c t s) := by sorry
