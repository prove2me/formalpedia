-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_22
-- name    : BS2_b3ba934b_Cert_40_RawPair1_22
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:23:47.882479+00:00
-- url     : https://prove2.me/theorems/ebce6890-b4d9-4e92-a043-7bf6b3d297a5
-- title:
--   Sensitivity separation: Endpoint40RawPair1_22 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_22. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_22.lean; original SHA-256 a6287634ed44fc667a9a2c250426e0001354c2bab6fd67ed97b82dfa8822f7a1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_22 : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
