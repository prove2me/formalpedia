-- Prove2me | Theorems.Thm_BSLambda_Final_bs_ge_real
-- name    : BSLambda.Final.bs_ge_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:19.556976+00:00
-- url     : https://prove2.me/theorems/ec40827d-3a50-4e0d-9fd6-8ee975a2b1d4
-- title:
--   Final: bs ge real
-- statement:
--   `bs_ge` cast into `ℝ`, the form in which the numeric comparisons below use it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L139-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L139-L139

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

theorem BSLambda.Final.bs_ge_real : (14011 : ℝ) ≤ (bs (ind Arc γ) : ℝ) := by sorry
