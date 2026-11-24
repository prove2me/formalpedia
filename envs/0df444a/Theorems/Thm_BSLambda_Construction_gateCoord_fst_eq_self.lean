-- Prove2me | Theorems.Thm_BSLambda_Construction_gateCoord_fst_eq_self
-- name    : BSLambda.Construction.gateCoord_fst_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:33.140808+00:00
-- url     : https://prove2.me/theorems/89b12647-9355-425f-9f54-67ec37a57592
-- title:
--   Construction: gate Coord fst eq self
-- statement:
--   A coordinate carrying the gate label of the arc `i → v.1` *is* that gate coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L78-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L78-L79

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

theorem BSLambda.Construction.gateCoord_fst_eq_self {γ : ι → ι → Fin r} {i : ι} {v : Coord ι r} (h : v.2 = γ i v.1) :
    gateCoord γ i v.1 = v := by sorry
