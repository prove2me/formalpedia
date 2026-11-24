-- Prove2me | Theorems.Thm_FockSPR_rho_pointwise_upper
-- name    : FockSPR.rho_pointwise_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:49.607503+00:00
-- url     : https://prove2.me/theorems/ddde6c5f-ebc0-454c-862c-96e0602fe00e
-- title:
--   Fock SPR: rho pointwise upper
-- statement:
--   `rho(w) ≤ rho(z) + ‖w − z‖`
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L64-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L64-L67

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR

theorem FockSPR.rho_pointwise_upper (w z : ℂ) : rho w ≤ rho z + ‖w - z‖ := by sorry
