-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_Cases3
-- name    : BS2_b3ba934b_Cert_16_Cases3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:32:45.17334+00:00
-- url     : https://prove2.me/theorems/be1b0150-6c66-417c-b504-dd9bdda7bde3
-- title:
--   Sensitivity separation: Endpoint16RawProof3 finite_cases checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof3.lean; original SHA-256 539c53bed447ae5c6ed37397bf1e9675200da15133afd04107cc772283d3f314; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_Cases3 : ∀ i j : Fin 16, i≤j →
    0<(recipe 3 j).tolerance → (recipe 3 j).tolerance≤2 →
    recipe 3 i=recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).1 ∧
    recipe 3 j=recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).2 ∧
    BS2_b3ba934b_Cert_16_Aux3.representativeBound3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)≤rawProfile3 (.a i j) := by sorry
