-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked2
-- name    : BS2_b3ba934b_Cert_16_AChecked2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:56.047328+00:00
-- url     : https://prove2.me/theorems/9ca00244-5d85-4810-aa64-475a66f15598
-- title:
--   Sensitivity separation: Endpoint16RawProof2 all_A_bounds checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof2.lean; original SHA-256 ec2d4c7f9e58f3aecbe5b2d18087140b7a8b5ae560a22e93d0a48061fde4862c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_AChecked2 (i j : Fin 16) (hij : i≤j) :
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by sorry
