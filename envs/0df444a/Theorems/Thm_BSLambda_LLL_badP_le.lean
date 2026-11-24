-- Prove2me | Theorems.Thm_BSLambda_LLL_badP_le
-- name    : BSLambda.LLL.badP_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:50.273733+00:00
-- url     : https://prove2.me/theorems/33794088-cb2d-42e9-b445-471ecb06f7fe
-- title:
--   LLL: bad P le
-- statement:
--   The two local-lemma inequalities of Section 10.2, in the shape required by
--   `pr_avoid_pos_two_type`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L767-L771
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L767-L771

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

theorem BSLambda.LLL.badP_le (t : Bool) :
    badP t ≤ badX t * (1 - badX false) ^ badD t false * (1 - badX true) ^ badD t true := by sorry
