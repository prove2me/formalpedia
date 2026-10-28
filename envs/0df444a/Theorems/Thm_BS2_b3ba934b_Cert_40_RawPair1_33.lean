-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_33
-- name    : BS2_b3ba934b_Cert_40_RawPair1_33
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:02:26.596121+00:00
-- url     : https://prove2.me/theorems/8e371381-1a6e-4612-a290-3e2748ecdd5e
-- title:
--   Sensitivity separation: Endpoint40RawPair1_33 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_33. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_33.lean; original SHA-256 4d6b1bcc0f66262f7a9748339cb3a72db8d8ff78b7f32e84c117cf1b395b75f8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_33 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 10)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by sorry
