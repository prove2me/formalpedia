-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_Cases0
-- name    : BS2_b3ba934b_Cert_16_Cases0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:31:04.225774+00:00
-- url     : https://prove2.me/theorems/93d1e636-2579-4a95-9e1a-5e8d59d27d1a
-- title:
--   Sensitivity separation: Endpoint16RawProof0 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof0.lean; original SHA-256 69fc765c38fd207decac7eddb39f39d683909d7ea74eed806ed2c3aa57dd71d2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_Cases0 : ∀ i j : Fin 16, i≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 i=recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j)).1 ∧
    recipe 0 j=recipe 0 (BS2_b3ba934b_Cert_16_Aux0.representative0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j)).2 ∧
    BS2_b3ba934b_Cert_16_Aux0.representativeBound0 (BS2_b3ba934b_Cert_16_Aux0.caseIndex0 i j)≤rawProfile0 (.a i j) := by sorry
