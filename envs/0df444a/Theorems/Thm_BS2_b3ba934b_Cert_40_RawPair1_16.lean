-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_16
-- name    : BS2_b3ba934b_Cert_40_RawPair1_16
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:30:59.51154+00:00
-- url     : https://prove2.me/theorems/19c33386-a926-4ab0-8baa-ebd28c68600c
-- title:
--   Sensitivity separation: Endpoint40RawPair1_16 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_16. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_16.lean; original SHA-256 7b7085f4c27707714f8dd494355f5b41962f1672fad711590d6641fcaab9501e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_16 : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 5)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
