-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked0
-- name    : BS2_b3ba934b_Cert_40_AChecked0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:13:29.337896+00:00
-- url     : https://prove2.me/theorems/569e8122-7eb4-4d4b-932a-9e4f99ecdd7a
-- title:
--   Sensitivity separation: Endpoint40RawProof0 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof0.lean; original SHA-256 7a31c8e6adad0d094c67f9734e9b91bcdce1bd75ee2ff74105e322d178af9e1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_AChecked0 (i j : Fin 40) (hij : i≤j) :
    (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by sorry
