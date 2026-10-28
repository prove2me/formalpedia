-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_15
-- name    : BS2_b3ba934b_Cert_40_RawPair1_15
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:12:59.095198+00:00
-- url     : https://prove2.me/theorems/afc158de-51d1-43ce-901b-2c2f519198d5
-- title:
--   Sensitivity separation: Endpoint40RawPair1_15 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_15. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_15.lean; original SHA-256 5c4ccb6290fee4bd0e0ac872be1b3d5ffd522786ce243dad8472910dafb224ee; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_15 : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 5)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
