-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leaf_injective
-- name    : DeciSigma1.Full.Closure.leaf_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:21.066837+00:00
-- url     : https://prove2.me/theorems/018179d4-2e1e-4625-a60d-ad4513809d1b
-- title:
--   Closure: leaf injective
-- statement:
--   The two leaf cones determine a tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L36-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L36-L43

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

theorem DeciSigma1.Full.Closure.leaf_injective (c : Fin n → Bool) :
    Function.Injective (fun t : Tree n => (leaf c t false, leaf c t true)) := by sorry
