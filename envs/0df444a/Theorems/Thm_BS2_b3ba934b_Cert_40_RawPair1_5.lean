-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_5
-- name    : BS2_b3ba934b_Cert_40_RawPair1_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:41:47.311001+00:00
-- url     : https://prove2.me/theorems/2d8ee06e-433e-4eda-b157-39a1b7e6de55
-- title:
--   Sensitivity separation: Endpoint40RawPair1_5 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_5. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_5.lean; original SHA-256 186ad7aa1573c169fb5456395c05068617e6e7ba051c2faa10554926736824c7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_5 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 3)).eval profile1≤139965930438622964580062000000000000000000000000000000000000000000000000 := by sorry
