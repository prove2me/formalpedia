-- Prove2me | Theorems.Thm_BSLambda_Final_card_idx
-- name    : BSLambda.Final.card_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:52.443859+00:00
-- url     : https://prove2.me/theorems/ec80e073-d920-4f71-ba68-a5f64f1f88c7
-- title:
--   Final: card idx
-- statement:
--   The tournament has `14011` vertices (Section 2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L82-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L82-L82

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

theorem BSLambda.Final.card_idx : Fintype.card Idx = 14011 := by sorry
