-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_Cases3
-- name    : BS2_b3ba934b_Cert_40_Cases3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:34:25.186994+00:00
-- url     : https://prove2.me/theorems/67a1ed65-eae3-41d0-8794-57bb151f7058
-- title:
--   Sensitivity separation: Endpoint40RawProof3 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof3.lean; original SHA-256 52106b0976aad197869ce9c3632aa349f775d54c498fea7ebf8933a746553dfe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Cert_40_Aux3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_Cases3 : ∀ i j : Fin 40, i≤j →
    0<(recipe 3 j).tolerance → (recipe 3 j).tolerance≤2 →
    recipe 3 i=recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).1 ∧
    recipe 3 j=recipe 3 (BS2_b3ba934b_Cert_40_Aux3.representative3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)).2 ∧
    BS2_b3ba934b_Cert_40_Aux3.representativeBound3 (BS2_b3ba934b_Cert_40_Aux3.caseIndex3 i j)≤rawProfile3 (.a i j) := by sorry
