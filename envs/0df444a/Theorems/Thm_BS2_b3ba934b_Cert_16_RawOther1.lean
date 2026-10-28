-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther1
-- name    : BS2_b3ba934b_Cert_16_RawOther1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:28:57.603405+00:00
-- url     : https://prove2.me/theorems/2702e432-29d3-4f3d-b0c7-eaffbfb8a14a
-- title:
--   Sensitivity separation: Endpoint16RawOther1 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawOther1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther1.lean; original SHA-256 5cfc302fce0e4d14d4a47fa202c3f7caaf42bf08b82fee71582d0fce6d06dfa1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawOther1 :
    (∀ i j : Fin 16, i≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)),
∀ coord : Coord 16, valid coord → raw 1 profile1 coord≤rawProfile1 coord) := by sorry
