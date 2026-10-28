-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_2
-- name    : BS2_b3ba934b_Cert_16_RawPair3_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:11.200729+00:00
-- url     : https://prove2.me/theorems/748b6cfa-30e1-4a5c-ac83-dc1cf2206a14
-- title:
--   Sensitivity separation: Endpoint16RawPair3_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_2.lean; original SHA-256 db90021943c59fbaff7ed2deee29b7008ecb654665394f75805cb43d36ae5e73; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_2 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 2) (recipe 3 3)).eval profile3≤65136953840227306262442285060000000000000000000000000000000000000000000000 := by sorry
