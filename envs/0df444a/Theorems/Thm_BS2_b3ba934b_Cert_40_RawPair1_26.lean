-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_26
-- name    : BS2_b3ba934b_Cert_40_RawPair1_26
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:39:56.429007+00:00
-- url     : https://prove2.me/theorems/5100abd9-351b-4359-9612-527f8edd8b64
-- title:
--   Sensitivity separation: Endpoint40RawPair1_26 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_26. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_26.lean; original SHA-256 eaef9971ffd7d916f2db5c0074aeefd1b04d332f721ce2e719ed6b14a9fe4ab8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_26 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 9)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by sorry
