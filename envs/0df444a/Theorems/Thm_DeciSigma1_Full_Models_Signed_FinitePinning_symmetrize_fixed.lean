-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_fixed
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:06.207799+00:00
-- url     : https://prove2.me/theorems/fe1fa41b-3995-48e6-8d11-5e1ea7ab889c
-- title:
--   Finite Pinning: symmetrize fixed
-- statement:
--   The Finite Pinning construction uses the symmetrize fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L104-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L104-L112

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_fixed (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) :
    Constraints.Signed.dual (FTree.toTree ∘ symmetrize c A D) =
      FTree.toTree ∘ symmetrize c A D := by sorry
