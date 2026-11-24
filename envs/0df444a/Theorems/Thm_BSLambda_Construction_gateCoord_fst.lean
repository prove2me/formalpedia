-- Prove2me | Theorems.Thm_BSLambda_Construction_gateCoord_fst
-- name    : BSLambda.Construction.gateCoord_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:50.025133+00:00
-- url     : https://prove2.me/theorems/07037a88-09df-489c-ba8e-f11986b78972
-- title:
--   Construction: gate Coord fst
-- statement:
--   The Construction construction uses the gate Coord fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L72-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L72-L72

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

theorem BSLambda.Construction.gateCoord_fst (γ : ι → ι → Fin r) (i j : ι) : (gateCoord γ i j).1 = j := by sorry

attribute [defeq] BSLambda.Construction.gateCoord_fst
