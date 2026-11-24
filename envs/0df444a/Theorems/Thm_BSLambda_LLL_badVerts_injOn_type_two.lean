-- Prove2me | Theorems.Thm_BSLambda_LLL_badVerts_injOn_type_two
-- name    : BSLambda.LLL.badVerts_injOn_type_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:53.887387+00:00
-- url     : https://prove2.me/theorems/782aecf3-f79b-421b-a32a-82de356808f7
-- title:
--   LLL: bad Verts inj On type two
-- statement:
--   A type-two bad event is determined by its vertex support, so the type-two neighbours of a
--   bad event are counted by their supports (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L249-L256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L249-L256

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

theorem BSLambda.LLL.badVerts_injOn_type_two (i : BadIdx Arc) :
    Set.InjOn badVerts
      (((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) : Set (BadIdx Arc)) := by sorry
