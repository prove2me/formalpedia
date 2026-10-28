-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_6
-- name    : BS2_b3ba934b_Cert_40_RawPair1_6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:43:52.26953+00:00
-- url     : https://prove2.me/theorems/fc6255ab-e714-4084-9342-0df0ed60e610
-- title:
--   Sensitivity separation: Endpoint40RawPair1_6 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_6. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_6.lean; original SHA-256 547d9b57d8f87d3c0dde2015f3bbf8e217c2fe4d42b8c13a0d00b0d28ce5372a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_6 : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 3)).eval profile1≤139965930438622964580062000000000000000000000000000000000000000000000000 := by sorry
