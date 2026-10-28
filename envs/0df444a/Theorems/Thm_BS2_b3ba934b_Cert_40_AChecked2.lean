-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked2
-- name    : BS2_b3ba934b_Cert_40_AChecked2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:29:30.245811+00:00
-- url     : https://prove2.me/theorems/d81e2444-9eb3-465c-9def-738e4c065928
-- title:
--   Sensitivity separation: Endpoint40RawProof2 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof2.lean; original SHA-256 5c3795e111da5588d9d11d9eefb7938f801835b24c79c5f7b8e2fc1a7db5327d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_AChecked2 (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by sorry
