-- Prove2me | Theorems.Thm_BSLambda_Final_lam_sq_le
-- name    : BSLambda.Final.lam_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:51.744828+00:00
-- url     : https://prove2.me/theorems/217ba970-80cd-4f02-a05f-a7757be02b90
-- title:
--   Final: lam sq le
-- statement:
--   **The spectral bound** (Sections 11–12): `lambda(f)^2 ≤ 7149 + 2 √150108`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L151-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L151-L153

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}

theorem BSLambda.Final.lam_sq_le (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ 2 ≤ U := by sorry
