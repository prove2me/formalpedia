-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked0
-- name    : BS2_b3ba934b_Cert_16_AChecked0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:13.811423+00:00
-- url     : https://prove2.me/theorems/b3ff2de3-ff5b-4fe8-955d-e895e0a6e850
-- title:
--   Sensitivity separation: Endpoint16RawProof0 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof0.lean; original SHA-256 69fc765c38fd207decac7eddb39f39d683909d7ea74eed806ed2c3aa57dd71d2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_AChecked0 (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by sorry
