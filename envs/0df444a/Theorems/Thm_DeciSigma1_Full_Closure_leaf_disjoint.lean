-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leaf_disjoint
-- name    : DeciSigma1.Full.Closure.leaf_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:22.061125+00:00
-- url     : https://prove2.me/theorems/8a641bc5-6b83-427b-9f64-3ac13e77ec83
-- title:
--   Closure: leaf disjoint
-- statement:
--   The Closure construction uses the leaf disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L79-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L79-L82

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Closure.leaf_disjoint (c : Fin n → Bool) (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ leaf c t false → w ∈ leaf c t true → False := by sorry
