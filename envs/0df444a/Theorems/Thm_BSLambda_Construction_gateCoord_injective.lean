-- Prove2me | Theorems.Thm_BSLambda_Construction_gateCoord_injective
-- name    : BSLambda.Construction.gateCoord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:45.410601+00:00
-- url     : https://prove2.me/theorems/75cf0044-3d34-41f7-a188-439453b2a0cc
-- title:
--   Construction: gate Coord injective
-- statement:
--   The Construction construction uses the gate Coord injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L74-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L74-L75

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

theorem BSLambda.Construction.gateCoord_injective (γ : ι → ι → Fin r) (i : ι) :
    Function.Injective (gateCoord γ i) := by sorry
