-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther3
-- name    : BS2_b3ba934b_Cert_16_RawOther3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:31:53.975751+00:00
-- url     : https://prove2.me/theorems/e60b813b-9c22-499e-8e98-5dcc193fa051
-- title:
--   Sensitivity separation: Endpoint16RawOther3 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawOther3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3.lean; original SHA-256 750533425cf29d19b5907b9cfe1f4a069e79ccecaec5771fcceb68f05d5f7786; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawOther3 :
    (∀ i j : Fin 16, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)),
∀ coord : Coord 16, valid coord → raw 3 profile3 coord≤rawProfile3 coord) := by sorry
