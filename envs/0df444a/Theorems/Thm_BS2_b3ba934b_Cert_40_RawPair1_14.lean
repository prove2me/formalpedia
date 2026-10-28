-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_14
-- name    : BS2_b3ba934b_Cert_40_RawPair1_14
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:10:48.06993+00:00
-- url     : https://prove2.me/theorems/1055aae9-9f8f-4013-a2b0-7185a3101bf2
-- title:
--   Sensitivity separation: Endpoint40RawPair1_14 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_14. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_14.lean; original SHA-256 8afe212e482a75deeb0bc7791d2661b3367e164b74db3905221618c0b5952c4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_14 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 5)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
