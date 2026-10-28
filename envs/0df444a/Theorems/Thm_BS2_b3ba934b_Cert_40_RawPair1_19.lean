-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_19
-- name    : BS2_b3ba934b_Cert_40_RawPair1_19
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:53:13.222361+00:00
-- url     : https://prove2.me/theorems/0a44de71-d936-4cb4-9e17-25f32e7a7f0e
-- title:
--   Sensitivity separation: Endpoint40RawPair1_19 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_19. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_19.lean; original SHA-256 4bf4d69d60203f8faec25828d2567eea2ded50029c4fcfbf2b4116cecda30517; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_19 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
