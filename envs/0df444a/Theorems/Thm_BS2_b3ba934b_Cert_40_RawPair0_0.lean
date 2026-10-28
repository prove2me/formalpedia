-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_0
-- name    : BS2_b3ba934b_Cert_40_RawPair0_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T22:29:46.57958+00:00
-- url     : https://prove2.me/theorems/9ec59ee9-42bb-48b9-8d41-f249736332e3
-- title:
--   Sensitivity separation: Endpoint40RawPair0_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair0_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_0.lean; original SHA-256 95fb9724908cb8fcabfda66ae34c16117b209d4cb8e68ad2b25d702bc023a527; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair0_0 : (rawAExpr 40 caps records (recipe 0 0) (recipe 0 1)).eval profile0≤77806142500417596074000000000000000000000000000000000000000000000000 := by sorry
