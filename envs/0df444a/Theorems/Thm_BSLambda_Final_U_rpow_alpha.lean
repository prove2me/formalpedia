-- Prove2me | Theorems.Thm_BSLambda_Final_U_rpow_alpha
-- name    : BSLambda.Final.U_rpow_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:22:01.072181+00:00
-- url     : https://prove2.me/theorems/e85d5b4c-354a-47e4-a690-7e1be775ec04
-- title:
--   Final: U rpow alpha
-- statement:
--   `U ^ (α/2) = 14011` (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L183-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L183-L190

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

theorem BSLambda.Final.U_rpow_alpha : U ^ (alpha / 2) = 14011 := by sorry
