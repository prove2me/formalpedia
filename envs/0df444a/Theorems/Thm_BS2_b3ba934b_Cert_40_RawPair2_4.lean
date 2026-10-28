-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_4
-- name    : BS2_b3ba934b_Cert_40_RawPair2_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:54:06.164896+00:00
-- url     : https://prove2.me/theorems/34c26fdb-7708-432d-8fdf-f0f09223a9d1
-- title:
--   Sensitivity separation: Endpoint40RawPair2_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_4.lean; original SHA-256 30ad0f2ed729d0ce5e74de117345ecf699cfb917567b1296ee0c133b1d954ead; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_4 : (rawAExpr 40 caps records (recipe 2 1) (recipe 2 3)).eval profile2≤333228916662993117187787030000000000000000000000000000000000000000000000 := by sorry
