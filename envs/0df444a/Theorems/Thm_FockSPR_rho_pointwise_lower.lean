-- Prove2me | Theorems.Thm_FockSPR_rho_pointwise_lower
-- name    : FockSPR.rho_pointwise_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:01.382558+00:00
-- url     : https://prove2.me/theorems/03ed6928-de0e-403e-92cb-5e0a470881be
-- title:
--   Fock SPR: rho pointwise lower
-- statement:
--   `rho(w) ≥ rho(z) − ‖w − z‖`
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L70-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L70-L73

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR

theorem FockSPR.rho_pointwise_lower (w z : ℂ) : rho w ≥ rho z - ‖w - z‖ := by sorry
