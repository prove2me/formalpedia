-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_8
-- name    : BS2_b3ba934b_Cert_40_RawPair1_8
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:48:28.622753+00:00
-- url     : https://prove2.me/theorems/422c2ea4-7555-45db-8aba-832bf4fa4c94
-- title:
--   Sensitivity separation: Endpoint40RawPair1_8 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_8. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_8.lean; original SHA-256 fa067c01a251c4532faa6652abe7cce22d6446635fb1c3c8737b69a86c202114; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_8 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 4)).eval profile1≤4440088403177649112679030000000000000000000000000000000000000000000000 := by sorry
