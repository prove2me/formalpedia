-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_2
-- name    : BS2_b3ba934b_Cert_40_RawPair1_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:29:41.727967+00:00
-- url     : https://prove2.me/theorems/48d97cad-e3d5-48b3-8863-312631b8f1a5
-- title:
--   Sensitivity separation: Endpoint40RawPair1_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_2.lean; original SHA-256 3d17c9fed96735730859f85376477dc525b08161e538c77dee1827d286e4fe18; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_2 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 2)).eval profile1≤139971226835560182197211160000000000000000000000000000000000000000000000 := by sorry
