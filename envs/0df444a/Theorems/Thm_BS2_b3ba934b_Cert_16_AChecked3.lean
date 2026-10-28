-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked3
-- name    : BS2_b3ba934b_Cert_16_AChecked3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:31:50.831056+00:00
-- url     : https://prove2.me/theorems/ac52fc37-eaf8-4f9e-b6fe-6cf9e887abf4
-- title:
--   Sensitivity separation: Endpoint16RawProof3 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof3.lean; original SHA-256 539c53bed447ae5c6ed37397bf1e9675200da15133afd04107cc772283d3f314; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_AChecked3 (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by sorry
