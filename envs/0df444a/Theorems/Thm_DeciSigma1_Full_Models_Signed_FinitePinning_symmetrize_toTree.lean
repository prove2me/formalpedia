-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_toTree
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_toTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:18:15.280894+00:00
-- url     : https://prove2.me/theorems/119ac73f-3b3b-4d2b-a7e7-18f87ccba746
-- title:
--   Finite Pinning: symmetrize to Tree
-- statement:
--   The Finite Pinning construction uses the symmetrize to Tree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L97-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L97-L102

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_toTree (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) :
    (symmetrize c A D z).toTree =
      treeMedian (A z).toTree (Constraints.Signed.dual (FTree.toTree ∘ A) z)
        (normalized c (FTree.toTree ∘ D) z) := by sorry
