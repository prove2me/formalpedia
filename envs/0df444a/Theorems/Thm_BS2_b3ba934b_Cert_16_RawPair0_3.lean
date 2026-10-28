-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_3
-- name    : BS2_b3ba934b_Cert_16_RawPair0_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:14.72827+00:00
-- url     : https://prove2.me/theorems/ab25b007-1e55-4929-ba67-cb5a597e1666
-- title:
--   Sensitivity separation: Endpoint16RawPair0_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair0_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair0_3.lean; original SHA-256 31080838a0c868c3954ecacde83d73b3f0f4c10816e25b2d3a95a23d9e2d2bde; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair0_3 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 1) (recipe 0 2)).eval profile0≤118398645020199144745000000000000000000000000000000000000000000000000 := by sorry
