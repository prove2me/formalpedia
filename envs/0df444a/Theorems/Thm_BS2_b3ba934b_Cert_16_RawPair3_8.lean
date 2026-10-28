-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_8
-- name    : BS2_b3ba934b_Cert_16_RawPair3_8
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:37.82841+00:00
-- url     : https://prove2.me/theorems/9a0c87f4-bc7a-4561-aab3-06ab1b06b899
-- title:
--   Sensitivity separation: Endpoint16RawPair3_8 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_8. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_8.lean; original SHA-256 365336f296eb0906aa3b0344bf36640857160753d3c58742179123d1bf4a2643; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_8 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 4) (recipe 3 4)).eval profile3≤550556636831362288633025143960000000000000000000000000000000000000000000000 := by sorry
