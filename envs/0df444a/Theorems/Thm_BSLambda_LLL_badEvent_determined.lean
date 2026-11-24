-- Prove2me | Theorems.Thm_BSLambda_LLL_badEvent_determined
-- name    : BSLambda.LLL.badEvent_determined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:53.982099+00:00
-- url     : https://prove2.me/theorems/f643ae7e-5b1d-498d-a937-c3ac65d66be0
-- title:
--   LLL: bad Event determined
-- statement:
--   Each bad event depends only on the arc variables internal to its own support
--   (Section 10).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L120-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L120-L124

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

theorem BSLambda.LLL.badEvent_determined (hT : IsTournament Arc) (i : BadIdx Arc) :
    Determined (β := fun _ : ι × ι => Fin r) (badSupp i) (badEvent (r := r) Arc i) := by sorry
