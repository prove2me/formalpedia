-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Pinning_finiteBoundPinning_fintype
-- name    : DeciSigma1.Full.Models.Pinning.finiteBoundPinning_fintype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:17.77257+00:00
-- url     : https://prove2.me/theorems/23d654b4-a79e-42ca-a50f-dd6fffcc2371
-- title:
--   Pinning: finite Bound Pinning fintype
-- statement:
--   Every flat constraint over a finite type of variables has the property
--   `FiniteBoundPinning`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L73-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L73-L93

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ}

theorem DeciSigma1.Full.Models.Pinning.finiteBoundPinning_fintype {V : Type*} [Finite V] (Γ : List (LitT n V)) :
    FiniteBoundPinning Γ := by sorry
