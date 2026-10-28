-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_35
-- name    : BS2_b3ba934b_Cert_40_RawPair1_35
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:08:27.728284+00:00
-- url     : https://prove2.me/theorems/53a6a0fb-96a2-4966-8980-c9812d5952a2
-- title:
--   Sensitivity separation: Endpoint40RawPair1_35 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_35. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_35.lean; original SHA-256 e9ae85e81f224b8826fe914dfd466dcf30f27bdd80144bdb8624340a07596b5e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_35 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 10)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by sorry
