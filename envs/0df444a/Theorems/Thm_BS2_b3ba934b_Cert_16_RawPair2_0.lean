-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_0
-- name    : BS2_b3ba934b_Cert_16_RawPair2_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:30.161493+00:00
-- url     : https://prove2.me/theorems/a0ba7951-5650-470c-9ef9-583d6e0b3b6b
-- title:
--   Sensitivity separation: Endpoint16RawPair2_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_0.lean; original SHA-256 c628281bc4c01f876f4d6290d2435a9e5e2d4a6446e1ddd1cdc6e738a43269d6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_0 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 0) (recipe 2 2)).eval profile2≤871561019159694584044656120000000000000000000000000000000000000000000000 := by sorry
