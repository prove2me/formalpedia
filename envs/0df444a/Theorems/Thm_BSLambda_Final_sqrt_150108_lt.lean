-- Prove2me | Theorems.Thm_BSLambda_Final_sqrt_150108_lt
-- name    : BSLambda.Final.sqrt_150108_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:54.056161+00:00
-- url     : https://prove2.me/theorems/4834cd9a-a535-4de7-86f5-d9289d59a41c
-- title:
--   Final: sqrt 150108 lt
-- statement:
--   `√150108 < 387.5`, the only numerical estimate needed in Section 12.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L156-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L156-L158

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

theorem BSLambda.Final.sqrt_150108_lt : Real.sqrt 150108 < 387.5 := by sorry
