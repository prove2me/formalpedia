-- Prove2me | Theorems.Thm_BSLambda_LLL_not_intObstruction_nine
-- name    : BSLambda.LLL.not_intObstruction_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:58.328103+00:00
-- url     : https://prove2.me/theorems/89e2bb1f-b4ca-4d32-be1e-be088e250855
-- title:
--   LLL: not int Obstruction nine
-- statement:
--   **Section 10.3**: a good configuration admits no radius-two internal obstruction on a
--   nine-element support, since such an obstruction puts `ω` into `radiusTwoEvent`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L815-L819
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L815-L819

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

theorem BSLambda.LLL.not_intObstruction_nine {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) (hobs : IntObstruction Arc 2 S h (toGamma ω)) : False := by sorry
