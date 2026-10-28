-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_3
-- name    : BS2_b3ba934b_Cert_16_RawPair2_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:49.117663+00:00
-- url     : https://prove2.me/theorems/bddf7ae3-cb63-4e26-aae6-5fbcfa486dde
-- title:
--   Sensitivity separation: Endpoint16RawPair2_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_3.lean; original SHA-256 1a0d02bc6b10b7bc924801dbc037f9d88ab39cfeae7afc437ea87099031257e9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_3 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 0) (recipe 2 3)).eval profile2≤661465889144801567244956340000000000000000000000000000000000000000000000 := by sorry
