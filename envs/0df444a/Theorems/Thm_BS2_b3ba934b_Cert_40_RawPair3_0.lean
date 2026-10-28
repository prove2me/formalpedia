-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_0
-- name    : BS2_b3ba934b_Cert_40_RawPair3_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:37:15.269977+00:00
-- url     : https://prove2.me/theorems/03f11344-5054-4742-b149-7627ca37cc64
-- title:
--   Sensitivity separation: Endpoint40RawPair3_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_0.lean; original SHA-256 fd37358d1a474f0b32cdb3ece96446123456c59e24ee7913ad49abc91c388b94; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_0 : (rawAExpr 40 caps records (recipe 3 0) (recipe 3 3)).eval profile3≤32945822928780164219782456170000000000000000000000000000000000000000000000 := by sorry
