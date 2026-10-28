-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther2
-- name    : BS2_b3ba934b_Cert_16_RawOther2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:13.473775+00:00
-- url     : https://prove2.me/theorems/4bc48cef-5e11-4079-a241-7e5b4d77283e
-- title:
--   Sensitivity separation: Endpoint16RawOther2 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawOther2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther2.lean; original SHA-256 a7410d5856ea725b45f942ccd5e7ef82da342bcbde32982e075648c16417cc55; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawOther2 :
    (∀ i j : Fin 16, i≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)),
∀ coord : Coord 16, valid coord → raw 2 profile2 coord≤rawProfile2 coord) := by sorry
