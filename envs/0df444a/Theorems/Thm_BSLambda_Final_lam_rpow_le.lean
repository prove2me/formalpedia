-- Prove2me | Theorems.Thm_BSLambda_Final_lam_rpow_le
-- name    : BSLambda.Final.lam_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:50.606626+00:00
-- url     : https://prove2.me/theorems/d0c66fa4-dea4-4cda-84c0-1329623a0e91
-- title:
--   Final: lam rpow le
-- statement:
--   **The separation for the seed** (Sections 12 and 14):
--   `lambda(f)^α ≤ 14011 ≤ bs(f)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L202-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L202-L207

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}

theorem BSLambda.Final.lam_rpow_le (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ alpha ≤ 14011 := by sorry
