-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_pins
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_pins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:07.5228+00:00
-- url     : https://prove2.me/theorems/01921adb-b3d4-4370-b833-5a9c39587f8a
-- title:
--   Finite Pinning: symmetrize pins
-- statement:
--   The Finite Pinning construction uses the symmetrize pins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L218-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L218-L225

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
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
open DeciSigma1.Full.Models.Signed.FinitePinning
variable {V : Type*}

theorem DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_pins {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → FTree n} (D : V → FTree n)
    (h : ∀ p ∈ pins c B, p.Holds (FTree.toTree ∘ A)) :
    ∀ p ∈ pins c B, p.Holds (FTree.toTree ∘ symmetrize c A D) := by sorry
