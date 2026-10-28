-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_6
-- name    : BS2_b3ba934b_Cert_40_RawPair2_6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:59:25.097281+00:00
-- url     : https://prove2.me/theorems/b98a970f-71e4-4c84-8b3a-960ee58699a0
-- title:
--   Sensitivity separation: Endpoint40RawPair2_6 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_6. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_6.lean; original SHA-256 9ce5c625a5cd84a0f7f3759d675e36a04bb176ce37bd03d2dc59d52676ddab89; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_6 : (rawAExpr 40 caps records (recipe 2 3) (recipe 2 3)).eval profile2≤4560729516651630895596915310000000000000000000000000000000000000000000000 := by sorry
