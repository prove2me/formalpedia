-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_2
-- name    : BS2_b3ba934b_Cert_40_RawPair0_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T22:29:35.23873+00:00
-- url     : https://prove2.me/theorems/d61e1cc1-fb0f-4d8e-8c03-a1ab93803e58
-- title:
--   Sensitivity separation: Endpoint40RawPair0_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair0_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_2.lean; original SHA-256 1a3e7c71df7c3abff33ca364ab6f695d05c3962627277bff6404fc6b286ad3bd; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair0_2 : (rawAExpr 40 caps records (recipe 0 0) (recipe 0 2)).eval profile0≤59055514859764786074000000000000000000000000000000000000000000000000 := by sorry
