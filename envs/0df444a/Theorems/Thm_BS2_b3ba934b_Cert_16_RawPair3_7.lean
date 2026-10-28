-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_7
-- name    : BS2_b3ba934b_Cert_16_RawPair3_7
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:27.002385+00:00
-- url     : https://prove2.me/theorems/0e59545a-25d2-45bf-a71d-96aadab3bfbd
-- title:
--   Sensitivity separation: Endpoint16RawPair3_7 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_7. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_7.lean; original SHA-256 324e13ecccfc9ab74b1741f245d6a270197de9a04914eef3f36c2ba324138af0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_7 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 3) (recipe 3 4)).eval profile3≤49435378198966834859642266240000000000000000000000000000000000000000000000 := by sorry
