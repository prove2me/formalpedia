-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_4
-- name    : BS2_b3ba934b_Cert_40_RawPair3_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:56:27.632431+00:00
-- url     : https://prove2.me/theorems/e19090a0-8ad2-43a3-98ac-ca2fa5d662e3
-- title:
--   Sensitivity separation: Endpoint40RawPair3_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_4.lean; original SHA-256 26d3a2784389c0bd0c53345bf76301d12638d34006625883b97d1bc569d4ec22; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_4 : (rawAExpr 40 caps records (recipe 3 0) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by sorry
