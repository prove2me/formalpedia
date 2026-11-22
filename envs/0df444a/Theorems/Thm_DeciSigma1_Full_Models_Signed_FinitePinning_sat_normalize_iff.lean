-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_sat_normalize_iff
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.sat_normalize_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:59.585804+00:00
-- url     : https://prove2.me/theorems/29c76af1-e0de-44d5-8b41-ad6dd98bf836
-- title:
--   Finite Pinning: sat normalize iff
-- statement:
--   The Finite Pinning construction uses the sat normalize iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L43-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L43-L46

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.sat_normalize_iff (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    SatT (fun _ => false) (normalized c ρ) (signed c Γ) ↔ SatT c ρ Γ := by sorry
