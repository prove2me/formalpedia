-- Prove2me | Theorems.Thm_BSLambda_LLL_two_le_card_inter_of_mem_nbr
-- name    : BSLambda.LLL.two_le_card_inter_of_mem_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:42.199851+00:00
-- url     : https://prove2.me/theorems/c1eafd2f-a169-48db-85f2-4f1e9a79b88f
-- title:
--   LLL: two le card inter of mem nbr
-- statement:
--   Two adjacent bad events have vertex supports meeting in at least two vertices: sharing a
--   gate variable forces sharing two vertices (Section 10).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L139-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L139-L142

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

theorem BSLambda.LLL.two_le_card_inter_of_mem_nbr {i j : BadIdx Arc}
    (h : j ∈ nbr (badSupp (Arc := Arc)) i) :
    2 ≤ (badVerts i ∩ badVerts j).card := by sorry
