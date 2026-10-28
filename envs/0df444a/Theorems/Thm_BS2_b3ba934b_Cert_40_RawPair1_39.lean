-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_39
-- name    : BS2_b3ba934b_Cert_40_RawPair1_39
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:27:51.252759+00:00
-- url     : https://prove2.me/theorems/f6c3f5a3-1ae9-4818-86dd-febd82a2367b
-- title:
--   Sensitivity separation: Endpoint40RawPair1_39 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_39. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_39.lean; original SHA-256 d8a170e59b5bc4844e81a7276d27f048c4ac930e43d9c2014d2cd525d558f5c6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_39 : (rawAExpr 40 caps records (recipe 1 7) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
