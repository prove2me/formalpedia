-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_sat_signDual
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.sat_signDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:18:45.34783+00:00
-- url     : https://prove2.me/theorems/f4a459c4-7931-4edf-9104-3a7561c5eafa
-- title:
--   Finite Pinning: sat sign Dual
-- statement:
--   The Finite Pinning construction uses the sat sign Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L48-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L48-L51

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.sat_signDual {c : Fin n → Bool} {A : V × Bool → Semantics.Tree n}
    {Γ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c Γ)) :
    SatT (fun _ => false) (Constraints.Signed.dual A) (signed c Γ) := by sorry
