-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_5
-- name    : BS2_b3ba934b_Cert_40_RawPair3_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:59:06.366728+00:00
-- url     : https://prove2.me/theorems/0c55fd5e-819d-4941-a2a7-709b036d7d97
-- title:
--   Sensitivity separation: Endpoint40RawPair3_5 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_5. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_5.lean; original SHA-256 75acd1e60d807a499396d235f25aa3b449411dd490c0ca3e269347e851c2b56d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_5 : (rawAExpr 40 caps records (recipe 3 1) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by sorry
