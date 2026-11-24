-- Prove2me | Theorems.Thm_BSLambda_Final_two_lt_alpha
-- name    : BSLambda.Final.two_lt_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:59.366126+00:00
-- url     : https://prove2.me/theorems/0acea47d-58ae-4e66-9ac9-4312273c5cb7
-- title:
--   Final: two lt alpha
-- statement:
--   **The exponent exceeds two** (Section 14): `α > 2`, because `U < 14011`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L177-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L177-L180

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

theorem BSLambda.Final.two_lt_alpha : 2 < alpha := by sorry
