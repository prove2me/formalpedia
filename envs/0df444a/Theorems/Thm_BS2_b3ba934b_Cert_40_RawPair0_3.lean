-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_3
-- name    : BS2_b3ba934b_Cert_40_RawPair0_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:03:56.309564+00:00
-- url     : https://prove2.me/theorems/0862edd5-b921-45e8-b22a-e1d21780e024
-- title:
--   Sensitivity separation: Endpoint40RawPair0_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair0_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_3.lean; original SHA-256 52dec57466abe0b2618c9b5bb067d2590838c9ce89d50495dbe30edb0b16bb2a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair0_3 : (rawAExpr 40 caps records (recipe 0 1) (recipe 0 2)).eval profile0≤59055514859764786074000000000000000000000000000000000000000000000000 := by sorry
