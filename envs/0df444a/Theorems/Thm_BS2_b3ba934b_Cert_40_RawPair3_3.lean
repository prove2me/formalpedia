-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_3
-- name    : BS2_b3ba934b_Cert_40_RawPair3_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:51:12.10546+00:00
-- url     : https://prove2.me/theorems/59262a14-7dfc-4d50-b19a-7dc9112e9c30
-- title:
--   Sensitivity separation: Endpoint40RawPair3_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_3.lean; original SHA-256 98215551d80052e7a2724ee6d19591845b5c0d6cca9f9b884bd2e3a929e1255f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_3 : (rawAExpr 40 caps records (recipe 3 3) (recipe 3 3)).eval profile3≤788367171188124766890095226590000000000000000000000000000000000000000000000 := by sorry
