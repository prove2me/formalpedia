-- Prove2me | Theorems.Thm_BSLambda_Final_ratio_gt
-- name    : BSLambda.Final.ratio_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:16.182841+00:00
-- url     : https://prove2.me/theorems/1081b55c-a714-4fb3-bebc-0f010ed3e691
-- title:
--   Final: ratio gt
-- statement:
--   The growth ratio exceeds `1.768` (Section 12).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L248-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L248-L250

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

theorem BSLambda.Final.ratio_gt : (1.768 : ℝ) < 14011 / U := by sorry
