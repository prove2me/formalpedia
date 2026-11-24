-- Prove2me | Theorems.Thm_BSLambda_Construction_cert_apply
-- name    : BSLambda.Construction.cert_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:23.978906+00:00
-- url     : https://prove2.me/theorems/41e9e1be-344c-45bd-a4e1-c463b1947314
-- title:
--   Construction: cert apply
-- statement:
--   The three-way case split describing `P_i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L97-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L97-L99

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

theorem BSLambda.Construction.cert_apply :
    cert Arc γ i v = if v.1 = i then some true
      else if Arc i v.1 ∧ v.2 = γ i v.1 then some false else none := by sorry
