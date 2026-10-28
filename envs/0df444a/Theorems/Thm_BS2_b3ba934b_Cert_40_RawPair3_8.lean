-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_8
-- name    : BS2_b3ba934b_Cert_40_RawPair3_8
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T07:06:42.315131+00:00
-- url     : https://prove2.me/theorems/5b201482-fa76-436a-afc9-d0503bee54ad
-- title:
--   Sensitivity separation: Endpoint40RawPair3_8 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_8. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_8.lean; original SHA-256 cda34b244e9f5bfadfd63276f308403e832089d9bd389d4ff46c43c84366fce9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_8 : (rawAExpr 40 caps records (recipe 3 4) (recipe 3 4)).eval profile3≤342172149755249424156185556300000000000000000000000000000000000000000000000 := by sorry
