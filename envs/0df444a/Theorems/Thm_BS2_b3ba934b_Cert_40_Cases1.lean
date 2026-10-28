-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_Cases1
-- name    : BS2_b3ba934b_Cert_40_Cases1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:18:54.888559+00:00
-- url     : https://prove2.me/theorems/8bd68d2d-6e12-482a-9cc5-2843ae93c953
-- title:
--   Sensitivity separation: Endpoint40RawProof1 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof1.lean; original SHA-256 72e59a2b0098ca1eccdc5e74fe2a14341af177f1a233bc3323d547569b5e1922; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_Cases1 : ∀ i j : Fin 40, i≤j →
    0<(recipe 1 j).tolerance → (recipe 1 j).tolerance≤2 →
    recipe 1 i=recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).1 ∧
    recipe 1 j=recipe 1 (BS2_b3ba934b_Cert_40_Aux1.representative1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux1.representativeBound1 (BS2_b3ba934b_Cert_40_Aux1.caseIndex1 i j)≤rawProfile1 (.a i j) := by sorry
