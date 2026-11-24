-- Prove2me | Theorems.Thm_BSLambda_Construction_cert_apply_eq_none
-- name    : BSLambda.Construction.cert_apply_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:52.363924+00:00
-- url     : https://prove2.me/theorems/9d2d4505-8cda-4382-9b0b-fc2376fe15c0
-- title:
--   Construction: cert apply eq none
-- statement:
--   Away from the owner block and from the outgoing gate coordinates, `P_i` is free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L120-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L120-L122

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

theorem BSLambda.Construction.cert_apply_eq_none (h₁ : v.1 ≠ i) (h₂ : ¬ (Arc i v.1 ∧ v.2 = γ i v.1)) :
    cert Arc γ i v = none := by sorry
