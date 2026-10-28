-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_10
-- name    : BS2_b3ba934b_Cert_40_RawPair1_10
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:56:17.120459+00:00
-- url     : https://prove2.me/theorems/479835cc-e258-4c88-89dd-9d6db6dc21bf
-- title:
--   Sensitivity separation: Endpoint40RawPair1_10 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_10. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_10.lean; original SHA-256 8bf3804f811550ead470550fa1ae22ce7be1caa77dc324d6c3551f51b63e09cb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_10 : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 4)).eval profile1≤49108527138416265322304030000000000000000000000000000000000000000000000 := by sorry
