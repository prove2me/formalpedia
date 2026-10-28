-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_Cases2
-- name    : BS2_b3ba934b_Cert_40_Cases2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:07:07.891126+00:00
-- url     : https://prove2.me/theorems/1800a986-57e6-4c6d-b9b1-75c8de6cc22f
-- title:
--   Sensitivity separation: Endpoint40RawProof2 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof2.lean; original SHA-256 5c3795e111da5588d9d11d9eefb7938f801835b24c79c5f7b8e2fc1a7db5327d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_Cases2 : ∀ i j : Fin 40, i≤j →
    0<(recipe 2 j).tolerance → (recipe 2 j).tolerance≤2 →
    recipe 2 i=recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).1 ∧
    recipe 2 j=recipe 2 (BS2_b3ba934b_Cert_40_Aux2.representative2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux2.representativeBound2 (BS2_b3ba934b_Cert_40_Aux2.caseIndex2 i j)≤rawProfile2 (.a i j) := by sorry
