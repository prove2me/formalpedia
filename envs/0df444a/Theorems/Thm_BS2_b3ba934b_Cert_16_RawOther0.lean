-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther0
-- name    : BS2_b3ba934b_Cert_16_RawOther0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:14.765218+00:00
-- url     : https://prove2.me/theorems/e523cc6b-cb4e-431f-9a46-df4e4cb9c891
-- title:
--   Sensitivity separation: Endpoint16RawOther0 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawOther0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0.lean; original SHA-256 e43c2c2d430e35a551e1096410b440e5cea661e02b2ff0db634f9823f369d6ad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawOther0 :
    (∀ i j : Fin 16, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)),
∀ coord : Coord 16, valid coord → raw 0 profile0 coord≤rawProfile0 coord) := by sorry
