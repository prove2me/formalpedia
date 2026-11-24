-- Prove2me | Theorems.Thm_BSLambda_Final_lam_iter_rpow_le_bs
-- name    : BSLambda.Final.lam_iter_rpow_le_bs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:12.485055+00:00
-- url     : https://prove2.me/theorems/4312b04d-df43-4a07-8ef1-e11965aa0d96
-- title:
--   Final: lam iter rpow le bs
-- statement:
--   **The separation for the iterates** (Section 14): `lambda(F_m)^α ≤ bs(F_m)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L219-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L219-L230

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

theorem BSLambda.Final.lam_iter_rpow_le_bs (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    lam (iterFun (ind Arc γ) m) ^ alpha ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by sorry
