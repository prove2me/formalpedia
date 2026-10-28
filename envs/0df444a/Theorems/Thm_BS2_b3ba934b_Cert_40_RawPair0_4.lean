-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair0_4
-- name    : BS2_b3ba934b_Cert_40_RawPair0_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:06:25.09499+00:00
-- url     : https://prove2.me/theorems/d574e92b-240a-4773-9d34-54bfed6f4f5c
-- title:
--   Sensitivity separation: Endpoint40RawPair0_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair0_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_4.lean; original SHA-256 6b2ea3a4fed51d0a124fefe0344db7aa01dc75c0c976166efcf536edec3d900a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair0_4 : (rawAExpr 40 caps records (recipe 0 2) (recipe 0 2)).eval profile0≤809387291765886661574000000000000000000000000000000000000000000000000 := by sorry
