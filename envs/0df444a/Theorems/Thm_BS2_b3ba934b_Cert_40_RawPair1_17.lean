-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_17
-- name    : BS2_b3ba934b_Cert_40_RawPair1_17
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:35:31.376439+00:00
-- url     : https://prove2.me/theorems/d987c2e6-d83f-47d2-ac4e-987fa8b6afe8
-- title:
--   Sensitivity separation: Endpoint40RawPair1_17 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_17. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_17.lean; original SHA-256 416155996af1646baf455d55a782069d3d1a87f4212d2e6d10203d15bda66e31; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_17 : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 5)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
