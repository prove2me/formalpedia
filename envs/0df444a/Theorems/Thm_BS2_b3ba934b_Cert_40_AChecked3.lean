-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked3
-- name    : BS2_b3ba934b_Cert_40_AChecked3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T07:31:00.619986+00:00
-- url     : https://prove2.me/theorems/8e9e734e-4fda-4f53-9908-70e69f56a295
-- title:
--   Sensitivity separation: Endpoint40RawProof3 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof3.lean; original SHA-256 52106b0976aad197869ce9c3632aa349f775d54c498fea7ebf8933a746553dfe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_AChecked3 (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by sorry
