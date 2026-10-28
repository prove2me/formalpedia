-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_1
-- name    : BS2_b3ba934b_Cert_40_RawPair2_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:34:18.641083+00:00
-- url     : https://prove2.me/theorems/5a6c5fe3-f7cb-4e35-8abf-d6b9a1c31fff
-- title:
--   Sensitivity separation: Endpoint40RawPair2_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_1.lean; original SHA-256 35ff001e2600659ddd307795fcb890057e8a539f3cab477b2dc391eb421af2ff; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_1 : (rawAExpr 40 caps records (recipe 2 1) (recipe 2 2)).eval profile2≤439022647791663747058857540000000000000000000000000000000000000000000000 := by sorry
