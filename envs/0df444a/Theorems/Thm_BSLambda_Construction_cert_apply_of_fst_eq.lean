-- Prove2me | Theorems.Thm_BSLambda_Construction_cert_apply_of_fst_eq
-- name    : BSLambda.Construction.cert_apply_of_fst_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:12.545772+00:00
-- url     : https://prove2.me/theorems/13473dce-9fd2-45f1-a969-99a4aeed3130
-- title:
--   Construction: cert apply of fst eq
-- statement:
--   Inside the owner block, `P_i` fixes the coordinate to `true`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L111-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L111-L112

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}

theorem BSLambda.Construction.cert_apply_of_fst_eq (h : v.1 = i) : cert Arc γ i v = some true := by sorry
