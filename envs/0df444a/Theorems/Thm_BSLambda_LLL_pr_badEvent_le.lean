-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_badEvent_le
-- name    : BSLambda.LLL.pr_badEvent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:02.084535+00:00
-- url     : https://prove2.me/theorems/52133c1d-14ef-4ef0-a19f-ae6100327270
-- title:
--   LLL: pr bad Event le
-- statement:
--   Each bad event of type `t` has probability at most `badP t` (Sections 8.1 and 9).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L127-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L127-L135

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

theorem BSLambda.LLL.pr_badEvent_le [NeZero r] (hT : IsTournament Arc) (hr : r = 144) (i : BadIdx Arc) :
    pr (β := fun _ : ι × ι => Fin r) (badEvent Arc i) ≤ badP (badTy i) := by sorry
