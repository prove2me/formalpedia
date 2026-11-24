-- Prove2me | Theorems.Thm_BSLambda_Final_rpow_1_06_lt
-- name    : BSLambda.Final.rpow_1_06_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:54.542801+00:00
-- url     : https://prove2.me/theorems/d2b62882-885c-45e3-bdd6-0bfecd5365d6
-- title:
--   Final: rpow 1 06 lt
-- statement:
--   `7924 ^ 1.06 < 14011` (Section 14).  Raising to the fiftieth power turns this into the integer
--   inequality `7924 ^ 53 < 14011 ^ 50`, which avoids estimating any logarithm.  It is the
--   quantitative form of `2.12 < alpha` (the true value being `2.1269738...`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L264-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L264-L267

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

theorem BSLambda.Final.rpow_1_06_lt : (7924 : ℝ) ^ (1.06 : ℝ) < 14011 := by sorry
