-- Prove2me | Theorems.Thm_BSLambda_Final_bs_div_lam_sq_ge
-- name    : BSLambda.Final.bs_div_lam_sq_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:22:01.125373+00:00
-- url     : https://prove2.me/theorems/7aa61ff0-a6e0-4f62-a892-83183028b4fb
-- title:
--   Final: bs div lam sq ge
-- statement:
--   **The ratio blows up** (Section 14): `bs(F_m) / lambda(F_m)^2 ≥ (14011/U)^m`, and
--   `14011/U > 1.768`.  This refutes `bs(f) = O(lambda(f)^2)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L234-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L234-L245

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

theorem BSLambda.Final.bs_div_lam_sq_ge (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
      ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by sorry
