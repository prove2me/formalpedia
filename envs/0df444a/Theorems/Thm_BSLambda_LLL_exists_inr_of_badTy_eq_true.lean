-- Prove2me | Theorems.Thm_BSLambda_LLL_exists_inr_of_badTy_eq_true
-- name    : BSLambda.LLL.exists_inr_of_badTy_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:57.399703+00:00
-- url     : https://prove2.me/theorems/c635abec-2b9b-4d5c-be7e-0602783274eb
-- title:
--   LLL: exists inr of bad Ty eq true
-- statement:
--   A bad event of type `true` is a nine-element vertex support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L89-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L89-L93

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
omit [Fintype ι]

theorem BSLambda.LLL.exists_inr_of_badTy_eq_true {j : BadIdx Arc} (hj : badTy j = true) :
    ∃ S : {S : Finset ι // S.card = 9}, j = Sum.inr S := by sorry
