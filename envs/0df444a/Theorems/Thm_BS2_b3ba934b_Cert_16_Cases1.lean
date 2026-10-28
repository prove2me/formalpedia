-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_Cases1
-- name    : BS2_b3ba934b_Cert_16_Cases1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:49.099574+00:00
-- url     : https://prove2.me/theorems/53278e27-6c3c-4843-8b44-042b0d4135ca
-- title:
--   Sensitivity separation: Endpoint16RawProof1 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof1.lean; original SHA-256 b1d515f7bedd1f571892779beb6a1d5900f6ae7d9d8a93901f49f5e18733d56a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_Cases1 : ∀ i j : Fin 16, i≤j →
    0<(recipe 1 j).tolerance → (recipe 1 j).tolerance≤2 →
    recipe 1 i=recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j)).1 ∧
    recipe 1 j=recipe 1 (BS2_b3ba934b_Cert_16_Aux1.representative1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j)).2 ∧
    BS2_b3ba934b_Cert_16_Aux1.representativeBound1 (BS2_b3ba934b_Cert_16_Aux1.caseIndex1 i j)≤rawProfile1 (.a i j) := by sorry
