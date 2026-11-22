-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_sat
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:17.369218+00:00
-- url     : https://prove2.me/theorems/372ef832-6c00-49ea-873f-f66bbe3f7a21
-- title:
--   Finite Pinning: symmetrize sat
-- statement:
--   The Finite Pinning construction uses the symmetrize sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L114-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L114-L120

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_sat {c : Fin n → Bool} {A : V × Bool → FTree n}
    {D : V → FTree n} {Γ : List (LitT n V)}
    (ha : SatT (fun _ => false) (FTree.toTree ∘ A) (signed c Γ))
    (hd : SatT c (FTree.toTree ∘ D) Γ) :
    SatT (fun _ => false) (FTree.toTree ∘ symmetrize c A D) (signed c Γ) := by sorry
