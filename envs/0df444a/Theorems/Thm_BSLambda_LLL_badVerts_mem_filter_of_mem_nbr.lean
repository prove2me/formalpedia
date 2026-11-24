-- Prove2me | Theorems.Thm_BSLambda_LLL_badVerts_mem_filter_of_mem_nbr
-- name    : BSLambda.LLL.badVerts_mem_filter_of_mem_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:51.747301+00:00
-- url     : https://prove2.me/theorems/6fb63020-2b98-44c8-983c-f6c7582644ec
-- title:
--   LLL: bad Verts mem filter of mem nbr
-- statement:
--   The vertex support of a type-two neighbour of a bad event is a nine-element set meeting
--   the event's own vertex set in at least two vertices (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L239-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L239-L245

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

theorem BSLambda.LLL.badVerts_mem_filter_of_mem_nbr {i j : BadIdx Arc}
    (hj : j ∈ (nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) :
    badVerts j ∈ Finset.univ.filter fun S : Finset ι =>
      S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card := by sorry
