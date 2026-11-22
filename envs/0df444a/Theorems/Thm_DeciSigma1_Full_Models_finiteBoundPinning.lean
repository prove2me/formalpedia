-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_finiteBoundPinning
-- name    : DeciSigma1.Full.Models.finiteBoundPinning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:18.843462+00:00
-- url     : https://prove2.me/theorems/ebb46763-661b-4d00-9a8f-ebeb0d191acb
-- title:
--   Models: finite Bound Pinning
-- statement:
--   Every flat constraint has the property `FiniteBoundPinning`, over any type of variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L135-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L135-L180

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Models.finiteBoundPinning {V : Type*} (Γ : List (LitT n V)) : FiniteBoundPinning Γ := by sorry
