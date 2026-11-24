-- Prove2me | Theorems.Thm_FockSPR_rho_le_norm
-- name    : FockSPR.rho_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:28.171546+00:00
-- url     : https://prove2.me/theorems/64b3eef8-2cde-4dab-9a35-8073e419cb0e
-- title:
--   Fock SPR: rho le norm
-- statement:
--   The Fock SPR construction uses the rho le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LipschitzRho.lean#L79-L81

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR

theorem FockSPR.rho_le_norm (w : ℂ) : rho w ≤ ‖w‖ := by sorry
