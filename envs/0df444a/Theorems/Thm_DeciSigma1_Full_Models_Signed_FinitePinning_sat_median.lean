-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_sat_median
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.sat_median
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:11.389718+00:00
-- url     : https://prove2.me/theorems/709f5b25-520c-451e-9420-9b9f36b34587
-- title:
--   Finite Pinning: sat median
-- statement:
--   The median of three covariant solutions of a flat constraint is a covariant solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L60-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L60-L89

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.sat_median {A B D : V → Semantics.Tree n} {Γ : List (LitT n V)}
    (ha : SatT (fun _ => false) A Γ) (hb : SatT (fun _ => false) B Γ)
    (hd : SatT (fun _ => false) D Γ) :
    SatT (fun _ => false) (fun v => treeMedian (A v) (B v) (D v)) Γ := by sorry
