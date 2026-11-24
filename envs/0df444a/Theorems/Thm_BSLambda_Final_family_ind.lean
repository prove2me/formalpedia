-- Prove2me | Theorems.Thm_BSLambda_Final_family_ind
-- name    : BSLambda.Final.family_ind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:35.545555+00:00
-- url     : https://prove2.me/theorems/28a17404-4dae-40c2-85a3-81c836a565d2
-- title:
--   Final: family ind
-- statement:
--   The indicator of the certificate family is definitionally the indicator
--   `Construction.ind` of the union of the certificate subcubes (Section 3.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L130-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L130-L130

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

theorem BSLambda.Final.family_ind (h₁ : ListOne γ) (h₂ : ListTwo γ) : (family γ h₁ h₂).ind = ind Arc γ := by sorry
