-- Prove2me | Theorems.Thm_BSLambda_Final_lam_rpow_212_lt_bs
-- name    : BSLambda.Final.lam_rpow_212_lt_bs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:22:00.47002+00:00
-- url     : https://prove2.me/theorems/5444d075-35fd-4961-8c1c-cb765ed0613f
-- title:
--   Final: lam rpow 212 lt bs
-- statement:
--   **`bs(f) > lambda(f)^2.12`** (Sections 5, 12 and 14).  This is `lam_rpow_le` with the
--   irrational exponent `alpha = 2.1269738...` replaced by the explicit rational `2.12`, and
--   with a strict inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L272-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L272-L279

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

theorem BSLambda.Final.lam_rpow_212_lt_bs (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    lam (ind Arc γ) ^ (2.12 : ℝ) < (bs (ind Arc γ) : ℝ) := by sorry
