-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_5
-- name    : BS2_b3ba934b_Cert_40_RawPair2_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:56:56.515063+00:00
-- url     : https://prove2.me/theorems/ac0f290b-e556-4b5b-8d25-7a9056caf469
-- title:
--   Sensitivity separation: Endpoint40RawPair2_5 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_5. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_5.lean; original SHA-256 f8c46bed5032f17ef7e401781ccd2e98890475882436a010d704e3e94dae8a29; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_5 : (rawAExpr 40 caps records (recipe 2 2) (recipe 2 3)).eval profile2≤333228916662993117187787030000000000000000000000000000000000000000000000 := by sorry
