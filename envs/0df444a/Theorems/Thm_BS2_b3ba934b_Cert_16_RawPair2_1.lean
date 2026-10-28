-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_1
-- name    : BS2_b3ba934b_Cert_16_RawPair2_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:11.263108+00:00
-- url     : https://prove2.me/theorems/9b195e27-6433-4459-9cc3-82da7aea6e69
-- title:
--   Sensitivity separation: Endpoint16RawPair2_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_1.lean; original SHA-256 a576d2830be745dca153939d5b96e6d29b1351887631b6a3aa93c9e25760a742; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_1 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 1) (recipe 2 2)).eval profile2≤871561019159694584044656120000000000000000000000000000000000000000000000 := by sorry
