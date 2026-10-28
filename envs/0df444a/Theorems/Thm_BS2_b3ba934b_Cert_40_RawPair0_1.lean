-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_1
-- name    : BS2_b3ba934b_Cert_40_RawPair0_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T00:56:55.741794+00:00
-- url     : https://prove2.me/theorems/185643ad-019c-49f5-ad97-18815d548fc1
-- title:
--   Sensitivity separation: Endpoint40RawPair0_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair0_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_1.lean; original SHA-256 84f84938713a510f500f7b7ddbd53e457180c95e9ce26e445ea20a62f6f1b9b6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair0_1 : (rawAExpr 40 caps records (recipe 0 1) (recipe 0 1)).eval profile0≤1865036319175702176328000000000000000000000000000000000000000000000000 := by sorry
