-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_regular_of_leaf
-- name    : DeciSigma1.Full.Closure.regular_of_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:30.250378+00:00
-- url     : https://prove2.me/theorems/8a222663-f3bf-400f-ab2e-df3ee460cdd1
-- title:
--   Closure: regular of leaf
-- statement:
--   A tree with regular leaf cones has finitely many distinct subtrees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L66-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L66-L81

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Full.Closure.regular_of_leaf (c : Fin n → Bool) {t : Tree n}
    (h : ∀ s, IsRegular (leaf c t s)) : (Characterization.subtrees t).Finite := by sorry
